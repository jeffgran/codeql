private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.controlflow.CfgNodes
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowDispatch
private import codeql.ruby.ast.internal.Module
private import codeql.ruby.ApiGraphs
private import codeql.ruby.frameworks.StandardLibrary

/// See https://api.rubyonrails.org/classes/ActiveRecord/Persistence.html
private string activeRecordPersistenceInstanceMethodName() {
  result =
    [
      "becomes", "becomes!", "decrement", "decrement!", "delete", "delete!", "destroy", "destroy!",
      "destroyed?", "increment", "increment!", "new_record?", "persisted?",
      "previously_new_record?", "reload", "save", "save!", "toggle", "toggle!", "touch", "update",
      "update!", "update_attribute", "update_column", "update_columns"
    ]
}

// Methods with these names are defined for all active record model instances,
// so they are unlikely to refer to a database field.
private predicate isBuiltInMethodForActiveRecordModelInstance(string methodName) {
  methodName = activeRecordPersistenceInstanceMethodName() or
  methodName = basicObjectInstanceMethodName() or
  methodName = objectInstanceMethodName()
}

/**
 * A `ClassDeclaration` for a class that inherits from `ActiveRecord::Base`. For example,
 *
 * ```rb
 * class UserGroup < ActiveRecord::Base
 *   has_many :users
 * end
 *
 * class SpecialUserGroup < UserGroup
 * end
 * ```
 */
class ActiveRecordModelClass extends ClassDeclaration {
  ActiveRecordModelClass() {
    // class Foo < ActiveRecord::Base
    // class Bar < Foo
    this.getSuperclassExpr() =
      [
        API::getTopLevelMember("ActiveRecord").getMember("Base"),
        // In Rails applications `ApplicationRecord` typically extends `ActiveRecord::Base`, but we
        // treat it separately in case the `ApplicationRecord` definition is not in the database.
        API::getTopLevelMember("ApplicationRecord")
      ].getASubclass().getAUse().asExpr().getExpr()
  }

  // Gets the class declaration for this class and all of its super classes
  private ModuleBase getAllClassDeclarations() {
    result = this.getModule().getSuperClass*().getADeclaration()
  }

  // attempts to get the database table name that corresponds to this class
  // Rails has some somewhat complicated logic for how it "magically" derives
  // the table name, but for the normal case it's pretty simple. It just
  // takes the model name and changes it from CamelCase to snake_case, and
  // pluralizes it. It can also be overridden explicitly by setting
  // `self.table_name = "some_table_name"`. This predicate could be expanded to
  // be more accurate but this does a pretty good job. It correctly got
  // 465 out of 730 = 64%. this could be improved by porting over more logic from rails,
  // some of which is noted below in TODOs
  string getDatabaseTableName() {
    // table name is overridden in the class explicitly
    exists(ActiveRecordModelClassMethodCall m |
      m.getReceiverClass() = this and
      m.getMethodName() = "table_name=" and
      result = m.getArgument(0).(AssignExpr).getRightOperand().(Literal).getValueText() // WTF? the method `.table_name=`.getArgument(0) returns an `AssignExpr`??
    )
    or

    // or this class directly inherits from AR::Base, use its class name as the table name
    not exists(ActiveRecordModelClassMethodCall m |
      m.getReceiverClass() = this and
      m.getMethodName() = "table_name="
    ) and
    (this.getSuperclassExpr() instanceof ApplicationRecordAccess or this.getSuperclassExpr() instanceof ApplicationRecordAccess) and
    result = pluralize(underscore(this.getName()))
    or

    // or this class inherits from another class which inherits from AR::Base, so use that class's table name (STI)
    // TODO we need to look for a `table_name=` on any modules in the scope heirarchy, not just the ultimate inheritor from AR:Base
    // TODO we also need to look for `def table_name; "foos"; end` I think
    not exists(ActiveRecordModelClassMethodCall m |
      m.getReceiverClass() = this and
      m.getMethodName() = "table_name="
    ) and
    exists(ActiveRecordModelClass other |
      other.getModule() = resolveConstantReadAccess(this.getSuperclassExpr()) |
      result = other.getDatabaseTableName()
    )
  }

  // kinda just for debugging. this gets the table name from schema.rb
  // that matches the table name we derived above
  string getSchemaTableName() {
    exists(SchemaRbTable table |
      table.getTableName() = this.getDatabaseTableName() and
      result = table.getTableName())
  }

  // gets a database column, aka a "field" of this activerecord class
  // it does this by matching the class's table name to the table
  // definition from schema.rb
  // TODO: now that we have the list of field names for each AR class,
  // we could add more predicates here like `getAFieldAccess`, `getAFieldAssignment`, etc
  // that would return DataFlow nodes. these would be super useful for tracking data
  // flowing into and out of the database
  string getAFieldName() {
    exists(SchemaRbTable table |
      table.getTableName() = this.getDatabaseTableName() and
      result = table.getAColumn().getColumnName()
    )
  }

  /**
   * Gets methods defined in this class that may access a field from the database.
   */
  Method getAPotentialFieldAccessMethod() {
    // It's a method on this class or one of its super classes
    result = this.getAllClassDeclarations().getAMethod() and
    // There is a value that can be returned by this method which may include field data
    exists(DataFlow::Node returned, ActiveRecordInstanceMethodCall cNode, MethodCall c |
      exprNodeReturnedFrom(returned, result) and
      cNode.flowsTo(returned) and
      c = cNode.asExpr().getExpr()
    |
      // The referenced method is not built-in, and...
      not isBuiltInMethodForActiveRecordModelInstance(c.getMethodName()) and
      (
        // ...The receiver does not have a matching method definition, or...
        not exists(
          cNode.getInstance().getClass().getAllClassDeclarations().getMethod(c.getMethodName())
        )
        or
        // ...the called method can access a field
        c.getATarget() = cNode.getInstance().getClass().getAPotentialFieldAccessMethod()
      )
    )
  }
}

bindingset[s]
string underscore(string s) {
  // adapted from https://github.com/rails/rails/blob/984c3ef2775781d47efa9f541ce570daa2434a80/activesupport/lib/active_support/inflector/methods.rb#L96-L104
  // TODO add acronyms inflections
  result = s.replaceAll("::", "/").regexpReplaceAll("([A-Z]+)(?=[A-Z][a-z])|([a-z\\d])(?=[A-Z])", "$1$2_").toLowerCase()
}

bindingset[s]
string pluralize(string s) {
  // super dumb for now. we'd have to import the inflections list(s) to make this smarter
  // see: https://github.com/rails/rails/blob/984c3ef2775781d47efa9f541ce570daa2434a80/activesupport/lib/active_support/inflections.rb
  result = s + "s"
}

/** A class method call whose receiver is an `ActiveRecordModelClass`. */
class ActiveRecordModelClassMethodCall extends MethodCall {
  private ActiveRecordModelClass recvCls;

  ActiveRecordModelClassMethodCall() {
    // e.g. Foo.where(...)
    recvCls.getModule() = resolveConstantReadAccess(this.getReceiver())
    or
    // e.g. Foo.joins(:bars).where(...)
    recvCls = this.getReceiver().(ActiveRecordModelClassMethodCall).getReceiverClass()
    or
    // e.g. self.where(...) within an ActiveRecordModelClass
    this.getReceiver() instanceof Self and
    this.getEnclosingModule() = recvCls
  }

  /** The `ActiveRecordModelClass` of the receiver of this method. */
  ActiveRecordModelClass getReceiverClass() { result = recvCls }
}

private Expr sqlFragmentArgument(MethodCall call) {
  exists(string methodName |
    methodName = call.getMethodName() and
    (
      methodName =
        [
          "delete_all", "delete_by", "destroy_all", "destroy_by", "exists?", "find_by", "find_by!",
          "find_or_create_by", "find_or_create_by!", "find_or_initialize_by", "find_by_sql", "from",
          "group", "having", "joins", "lock", "not", "order", "pluck", "where", "rewhere", "select",
          "reselect", "update_all"
        ] and
      result = call.getArgument(0)
      or
      methodName = "calculate" and result = call.getArgument(1)
      or
      methodName in ["average", "count", "maximum", "minimum", "sum"] and
      result = call.getArgument(0)
      or
      // This format was supported until Rails 2.3.8
      methodName = ["all", "find", "first", "last"] and
      result = call.getKeywordArgument("conditions")
      or
      methodName = "reload" and
      result = call.getKeywordArgument("lock")
    )
  )
}

// An expression that, if tainted by unsanitized input, should not be used as
// part of an argument to an SQL executing method
private predicate unsafeSqlExpr(Expr sqlFragmentExpr) {
  // Literals containing an interpolated value
  sqlFragmentExpr.(StringlikeLiteral).getComponent(_) instanceof StringInterpolationComponent
  or
  // String concatenations
  sqlFragmentExpr instanceof AddExpr
  or
  // Variable reads
  sqlFragmentExpr instanceof VariableReadAccess
  or
  // Method call
  sqlFragmentExpr instanceof MethodCall
}

/**
 * A method call that may result in executing unintended user-controlled SQL
 * queries if the `getSqlFragmentSinkArgument()` expression is tainted by
 * unsanitized user-controlled input. For example, supposing that `User` is an
 * `ActiveRecord` model class, then
 *
 * ```rb
 * User.where("name = '#{user_name}'")
 * ```
 *
 * may be unsafe if `user_name` is from unsanitized user input, as a value such
 * as `"') OR 1=1 --"` could result in the application looking up all users
 * rather than just one with a matching name.
 */
class PotentiallyUnsafeSqlExecutingMethodCall extends ActiveRecordModelClassMethodCall {
  // The SQL fragment argument itself
  private Expr sqlFragmentExpr;

  PotentiallyUnsafeSqlExecutingMethodCall() {
    exists(Expr arg |
      arg = sqlFragmentArgument(this) and
      unsafeSqlExpr(sqlFragmentExpr) and
      (
        sqlFragmentExpr = arg
        or
        sqlFragmentExpr = arg.(ArrayLiteral).getElement(0)
      ) and
      // Check that method has not been overridden
      not exists(SingletonMethod m |
        m.getName() = this.getMethodName() and
        m.getOuterScope() = this.getReceiverClass()
      )
    )
  }

  Expr getSqlFragmentSinkArgument() { result = sqlFragmentExpr }
}

/**
 * An `SqlExecution::Range` for an argument to a
 * `PotentiallyUnsafeSqlExecutingMethodCall` that may be vulnerable to being
 * controlled by user input.
 */
class ActiveRecordSqlExecutionRange extends SqlExecution::Range {
  ActiveRecordSqlExecutionRange() {
    exists(PotentiallyUnsafeSqlExecutingMethodCall mc |
      this.asExpr().getNode() = mc.getSqlFragmentSinkArgument()
    )
  }

  override DataFlow::Node getSql() { result = this }
}

// TODO: model `ActiveRecord` sanitizers
// https://api.rubyonrails.org/classes/ActiveRecord/Sanitization/ClassMethods.html
/**
 * A node that may evaluate to one or more `ActiveRecordModelClass` instances.
 */
abstract class ActiveRecordModelInstantiation extends OrmInstantiation::Range,
  DataFlow::LocalSourceNode {
  abstract ActiveRecordModelClass getClass();

  bindingset[methodName]
  override predicate methodCallMayAccessField(string methodName) {
    // The method is not a built-in, and...
    not isBuiltInMethodForActiveRecordModelInstance(methodName) and
    (
      // ...There is no matching method definition in the class, or...
      not exists(this.getClass().getMethod(methodName))
      or
      // ...the called method can access a field.
      exists(Method m | m = this.getClass().getAPotentialFieldAccessMethod() |
        m.getName() = methodName
      )
    )
  }
}

// Names of class methods on ActiveRecord models that may return one or more
// instances of that model. This also includes the `initialize` method.
// See https://api.rubyonrails.org/classes/ActiveRecord/FinderMethods.html
private string finderMethodName() {
  exists(string baseName |
    baseName =
      [
        "fifth", "find", "find_by", "find_or_initialize_by", "find_or_create_by", "first",
        "forty_two", "fourth", "last", "second", "second_to_last", "take", "third", "third_to_last"
      ] and
    result = baseName + ["", "!"]
  )
  or
  result = "new"
}

// Gets the "final" receiver in a chain of method calls.
// For example, in `Foo.bar`, this would give the `Foo` access, and in
// `foo.bar.baz("arg")` it would give the `foo` variable access
private Expr getUltimateReceiver(MethodCall call) {
  exists(Expr recv |
    recv = call.getReceiver() and
    (
      result = getUltimateReceiver(recv)
      or
      not recv instanceof MethodCall and result = recv
    )
  )
}

// A call to `find`, `where`, etc. that may return active record model object(s)
private class ActiveRecordModelFinderCall extends ActiveRecordModelInstantiation, DataFlow::CallNode {
  private MethodCall call;
  private ActiveRecordModelClass cls;
  private Expr recv;

  ActiveRecordModelFinderCall() {
    call = this.asExpr().getExpr() and
    recv = getUltimateReceiver(call) and
    resolveConstant(recv) = cls.getAQualifiedName() and
    call.getMethodName() = finderMethodName()
  }

  final override ActiveRecordModelClass getClass() { result = cls }
}

// A `self` reference that may resolve to an active record model object
private class ActiveRecordModelClassSelfReference extends ActiveRecordModelInstantiation {
  private ActiveRecordModelClass cls;

  ActiveRecordModelClassSelfReference() {
    exists(Self s |
      s.getEnclosingModule() = cls and
      s.getEnclosingMethod() = cls.getAMethod() and
      s = this.asExpr().getExpr()
    )
  }

  final override ActiveRecordModelClass getClass() { result = cls }
}

// A (locally tracked) active record model object
private class ActiveRecordInstance extends DataFlow::Node {
  private ActiveRecordModelInstantiation instantiation;

  ActiveRecordInstance() { this = instantiation or instantiation.flowsTo(this) }

  ActiveRecordModelClass getClass() { result = instantiation.getClass() }
}

// A call whose receiver may be an active record model object
private class ActiveRecordInstanceMethodCall extends DataFlow::CallNode {
  private ActiveRecordInstance instance;

  ActiveRecordInstanceMethodCall() { this.getReceiver() = instance }

  ActiveRecordInstance getInstance() { result = instance }
}



// a schema definition
// e.g. https://github.com/gothinkster/rails-realworld-example-app/blob/master/db/schema.rb#L14
class SchemaRbDefinition extends DataFlow::CallNode {
  SchemaRbDefinition() {
    this = API::getTopLevelMember("ActiveRecord").getMember("Schema").getAMethodCall("define")
  }
}

// a table definition within the schema definition:
// e.g. https://github.com/gothinkster/rails-realworld-example-app/blob/master/db/schema.rb#L16
class SchemaRbTable extends DataFlow::CallNode {
  SchemaRbDefinition schema;

  SchemaRbTable() {
    this.getMethodName() = "create_table" and
    this.asExpr().getExpr().getEnclosingCallable() = schema.asExpr().getExpr().(MethodCall).getBlock()
  }

  string getTableName() {
    result = this.getArgument(0).asExpr().getExpr().getValueText()
  }

  DataFlow::Node getTableBlockParameter() {
    exists(LocalVariableAccess t, DataFlow::Node node |
      node.asExpr().getExpr() = t and
      t = this.asExpr().getExpr().(MethodCall).getBlock().getParameter(0).getAVariable().getAnAccess() and
      result = node
    )
  }

  // gets a column definition belonging to this table
  SchemaRbColumn getAColumn() {
    exists(SchemaRbColumn col |
      col.getTable() = this and
      result = col
    )
  }
}

// a column definition
// e.g. https://github.com/gothinkster/rails-realworld-example-app/blob/master/db/schema.rb#L17
class SchemaRbColumn extends DataFlow::CallNode {
  SchemaRbTable table;
  MethodCall call;

  SchemaRbColumn() {
    not this.getMethodName() = ["index"] and // probably missing some other exceptions.
    this.asExpr().getExpr() = call and
    call.getEnclosingCallable() = table.asExpr().getExpr().(MethodCall).getBlock() and
    this.getReceiver() = table.getTableBlockParameter()
  }

  string getColumnName() {
    result = this.getArgument(0).asExpr().getExpr().getValueText()
  }

  // TODO we have more information here, like the type of column, nullability, etc
  // we could add more helpful predicates here for that stuff.

  SchemaRbTable getTable() {
    result = table
  }
}
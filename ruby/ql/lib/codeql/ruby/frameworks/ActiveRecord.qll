private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.controlflow.CfgNodes
private import codeql.ruby.DataFlow
private import codeql.ruby.dataflow.internal.DataFlowDispatch
private import codeql.ruby.ast.internal.Module
private import codeql.ruby.ApiGraphs
private import codeql.ruby.frameworks.StandardLibrary

private class ActiveRecordBaseAccess extends ConstantReadAccess {
  ActiveRecordBaseAccess() {
    this.getName() = "Base" and
    this.getScopeExpr().(ConstantAccess).getName() = "ActiveRecord"
  }
}

// ApplicationRecord extends ActiveRecord::Base, but we
// treat it separately in case the ApplicationRecord definition
// is not in the database
private class ApplicationRecordAccess extends ConstantReadAccess {
  ApplicationRecordAccess() { this.getName() = "ApplicationRecord" }
}

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
 * A `ClassDeclaration` for a class that extends `ActiveRecord::Base`. For example,
 *
 * ```rb
 * class UserGroup < ActiveRecord::Base
 *   has_many :users
 * end
 * ```
 */
class ActiveRecordModelClass extends ClassDeclaration {
  ActiveRecordModelClass() {
    // class Foo < ActiveRecord::Base
    this.getSuperclassExpr() instanceof ActiveRecordBaseAccess
    or
    // class Foo < ApplicationRecord
    this.getSuperclassExpr() instanceof ApplicationRecordAccess
    or
    // class Bar < Foo
    exists(ActiveRecordModelClass other |
      other.getModule() = resolveConstantReadAccess(this.getSuperclassExpr())
    )
  }

  // Gets the class declaration for this class and all of its super classes
  private ModuleBase getAllClassDeclarations() {
    result = this.getModule().getSuperClass*().getADeclaration()
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
  exists(StringInterpolationComponent interpolated |
    interpolated = sqlFragmentExpr.(StringlikeLiteral).getComponent(_)
  )
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
class ActiveRecordModelFinderCall extends ActiveRecordModelInstantiation, DataFlow::CallNode {
  private MethodCall call;
  private ActiveRecordModelClass cls;
  private Expr recv;

  ActiveRecordModelFinderCall() {
    call = this.asExpr().getExpr() and

    // This will result in misleading/incorrect/false positive results.
    // This gets the ultimate receiver of a chain, but the ultimate reciever of a chain
    // is not necessarily the correct model class, and often is not. For example:
    // ```
    // class Foo < ApplicationRecord
    //   has_many :bars
    // end
    // class Bar < ApplicationRecord
    //   belongs_to :foo
    // end
    // mymodel = Foo.find(id).bars.first
    // ```
    // In this code, mymodel is an instance of `Bar`, not `Foo`, but this code would detect it as a `Foo`.
    //
    // The popular Ruby SAST tool Brakeman does this same exact thing. See:
    // https://github.com/presidentbeef/brakeman/blob/main/lib/brakeman/checks/check_mass_assignment.rb#L39-L51
    // In that code, the `:chained => true` is doing this exact same thing, and makes this same error.
    // What I want from CodeQL is to be better than brakeman, because I know it has the power to do so,
    // but as of yet this is making the same mistake, here at least.
    recv = getUltimateReceiver(call) and

    // this line fails to match many of our classes because they are declared like
    // ```
    // class Namespace::MyModel < ApplicationRecord
    // end
    // ```
    // ...and getQualifiedName() does not resolve the fully qualified name of that class properly
    resolveConstant(recv) = cls.getQualifiedName() and


    call.getMethodName() = finderMethodName()
  }


  // added these methods so i could output the values to help debug why my query wasn't working right.
  string getMethodName() {
    result = call.getMethodName()
  }

  string getQualifiedClassName() {
    result = cls.getQualifiedName()
  }

  string getClassName() {
    result = resolveConstant(recv)
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
class ActiveRecordInstance extends DataFlow::Node {
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

//*******************************************************************************
//                                      JG
//*******************************************************************************

// a method call on an active record class.
class ActiveRecordClassMethodCall extends DataFlow::CallNode {
  ActiveRecordModelClass cls;
  ActiveRecordClassMethodCall() { this.getReceiver().asExpr().getExpr() instanceof ActiveRecordModelClass }
}

// the declarative class method called in an active record class to define
// a column to be an "attachment" column managed by the paperclip gem.
// for example:
// ```
// class Foo < ApplicationRecord
//   has_attached_file :logo, some_option: :whatever
// end
// ```
class PaperclipHasAttachedFileCall extends ActiveRecordModelClassMethodCall {
  PaperclipHasAttachedFileCall() {
    this.getMethodName() = "has_attached_file"
  }

  // gets the name of the column that represents a file attachment.
  // in the example:
  // ```
  // class Foo < ApplicationRecord
  //   has_attached_file :logo
  // end
  // ```
  // ... this would return the string "logo"
  string getAttachmentColumnName() {
    result = this.getArgument(0).(SymbolLiteral).getValueText()
  }
}

// matches the subset of `ActiveRecordModelClass`es that have a paperclip attachment column defined
class PaperclipEnabledActiveRecordClass extends ActiveRecordModelClass {
  PaperclipHasAttachedFileCall call;

  PaperclipEnabledActiveRecordClass() {
    call.getReceiverClass() = this
  }

  string getAttachmentColumnName() { result = call.getAttachmentColumnName() }
}

// a call on an active record model class that can "mass assign" data to fields, in the form of a ruby hash,
// example:
// `my_new_foo = Foo.new({field: "value", other_field: "other value"})`
// or,
// `my_new_bar = Foo.find(id).bars.build({field: "value", other_field: "other value"})`
class MassAssignmentCall extends ActiveRecordModelClassMethodCall {
  MassAssignmentCall() {
    this.getMethodName() = ["new", "create", "create!", "build", "find_or_create_by", "find_or_create_by!",
    "find_or_initialize_by", "first_or_create", "first_or_create!", "first_or_initialize"]
  }
}

class MassAssignmentToPaperclipClass extends MassAssignmentCall {
  PaperclipEnabledActiveRecordClass cls;
  MassAssignmentToPaperclipClass() {
    this.getReceiverClass() = cls
  }
}


// this class is an attempt to define an extension of `HTTP::Client::Request::Range`
// which will detect user input being assigned to a paperclip attachment column.
// If the user supplies a URL, Paperclip will fetch that url and use the result as the attachment.
// This can cause an SSRF vulnerability if the user supplies a URL that maps to an internal resource or something.
//
// This was modeled as an `HTTP::Client::Request::Range` for simplicity since then the existing
// SSRF query will pick this up. However, it's a little bit of a mis-fit because really we're just
// doing an `assignment` operation here, so it's a little wonky to pretend assigning a value to a field
// is a network client request. But it serves the purpose.
class PaperclipAssignment extends HTTP::Client::Request::Range {
  DataFlow::CallNode assignment;

  PaperclipAssignment() {
    exists(API::Node apiNode, ActiveRecordInstance instance, PaperclipEnabledActiveRecordClass paperclass |
      assignment = apiNode.getAnImmediateUse() and
      this = assignment.asExpr().getExpr()
    |
      // match a method call on an active record instance
      assignment.getReceiver() = instance and

      // the method call should be some kind of assignment of data. this is overly broad currently, and
      // should only match if the specific column is being assigned, like:
      // `foo.logo= "bad url"`
      // `foo.update_column(:logo, "bad url")`
      // `foo.update({logo: "bad url"})`
      // `foo.update_attributes({logo: "bad url"})`
      assignment.getMethodName() = [paperclass.getAttachmentColumnName()+"=", "update", "update_column", "update_attributes"] and

      // the class of the active record instance must be a class that has a paperclip attachment column defined
      assignment.getReceiver().(ActiveRecordInstance).getClass() = paperclass
    )
    or
    exists(API::Node apiNode, MassAssignmentToPaperclipClass masscall |
      assignment = apiNode.getAnImmediateUse() and
      this = assignment.asExpr().getExpr()
      |
      // match a "mass assignment" call to an active record model class that has
      // a paperclip attachment column defined. Again this is overly broad currently. We need to narrow
      // to select the mass assignment only when the paperclip column name is one of the keys provided
      // to the mass assignment call
      assignment.asExpr().getExpr().(MethodCall) = masscall
    )
  }

  string getAssignmentMethodName() {
    result = assignment.getMethodName()
  }

  // these have dummy values for now, for debugging the query.
  // getURL() would need to select the RHS of the assignment (narrowed to just the hash key that matches the
  // paperclip column name, in the case of a mass assignment as opposed to a direct assignment of the field itself)
  override DataFlow::Node getURL() { result = assignment }
  override DataFlow::Node getResponseBody() { result = assignment }

  override string getFramework() {
    result = "Paperclip"
  }

  override predicate disablesCertificateValidation(DataFlow::Node disablingNode) { not exists(disablingNode) }
}

import { map, tap, catchError } from 'rxjs/operators';

source()
    .pipe(
        map(x => x + 'foo'),
        map(x => x + 'bar'),
        catchError(err => {})
    )
    .subscribe(data => {
        sink(data)
    });

source()
    .pipe(
        map(x => x + 'foo'),
        // `tap` taps into the source observable, so like `subscribe` but inside the pipe.
        tap(x => sink(x)),
        tap(x => sink(x)),
        catchError(err => {})
    )
    .subscribe(data => {
        sink(data)
    });

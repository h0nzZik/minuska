@frames: [];
@value(X): (is_true(bool.false())) ;
@nonvalue(X): (is_true(bool.true())) ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[X] => state[X, [(@builtin-int 0)]] where [] ;

@rule [step]: state[M, N] => state[z.minus(M, [(@builtin-int 1)]), z.plus(N, M)] where [is_true(z.lt([(@builtin-int 0)], M))] ;




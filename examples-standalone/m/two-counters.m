@frames: [];
@value(X): (bool.false()) ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[X] => state[X, [(@builtin-int 0)]] where bool.true() ;

@rule [step]: state[M, N] => state[z.minus(M, [(@builtin-int 1)]), z.plus(N, M)] where z.lt([(@builtin-int 0)], M) ;




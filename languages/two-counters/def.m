@frames: [];
@value(X): @false ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[] => state[program.ast(), [(@builtin:int("0"))]] where @true ;

@rule [step]: state[M, N] => state[z.minus(M, [(@builtin:int("1"))]), z.plus(N, M)] where bool.is_true(z.lt([(@builtin:int("0"))], M)) ;




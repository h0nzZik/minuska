@frames: [];
@value(X): (bool.false()) ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[X] => cfg[X] where bool.true() ;

@rule [decrement]:
	cfg[X] => cfg[z.minus(X, [(@builtin 1)])] where bool.true()
    ;




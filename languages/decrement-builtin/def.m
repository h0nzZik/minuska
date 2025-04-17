@frames: [];
@value(X): @false ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[] => cfg[@query:program.ast()] where @true ;

@rule [decrement]:
	cfg[X] => cfg[z.minus(X, [(@builtin:int("1"))])] where @true
    ;




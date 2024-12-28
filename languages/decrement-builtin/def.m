@frames: [];
@value(X): (is_true(bool.false())) ;
@nonvalue(X): (is_true(bool.true())) ;
@context(HOLE): cfg [ HOLE ];
@strictness: [];

@rule [init]: builtin.init[] => cfg[program.ast()] where [] ;

@rule [decrement]:
	cfg[X] => cfg[z.minus(X, [(@builtin-int 1)])] where []
    ;




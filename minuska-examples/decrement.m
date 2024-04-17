symbols : [zero, succ] ;

value(X): (bool.false()) ;

strictness: [] ;

rule [decrement]:
	succ[X] => X where bool.true()
    ;




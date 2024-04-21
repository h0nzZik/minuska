symbols : [s] ;

value(X): (bool.or(bool.false(), bool.or(bool.false(), term.same_symbol(X, [unitValue[]])))) ;

strictness: [] ;

rule [stmt.ite.false]:
	ite[B,X,Y] => Y where bool.eq(B, bool.false())
    ;

rule [while.unfold]:
	while[B,X] => ite[B, seq[X, while[B, X]], unitValue[]]
	where bool.true()
	;





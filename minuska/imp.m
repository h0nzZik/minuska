symbols : plus, minus, ite, while, unitValue ;

value(X): bool.or(z.is(X), bool.or(bool.is(X), symbol.is(unitValue[], X))) ;


strictness: plus of arity 3 in [0,1] ;
rule/simple plus-z-z: plus[X,Y] =>{a} z.plus(X, Y) where bool.and(z.is(X), z.is(Y)) ;

rule/simple [stmt-ite-true]:
	ite[B,X,Y] => X where B ;

rule/simple [stmt-ite-false]:
	ite[B,X,Y] => Y where bool.eq(B, bool.false) ;

rule [while-unfold]:
	while[B,X] => ite[B, seq[X, while[B, X]], unitValue[]]
	where bool.true()
	;



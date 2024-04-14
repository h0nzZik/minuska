symbols: plus, minus, ite, while, unitValue ;

value(x): bool.or(Z.is(x), Bool.or(Bool.is(x), Symbol.is(unitValue, x))) ;


strictness: plus of arity 3 in [0,1] ;
rule/simple plus-Z-Z: plus[X,Y] =>{a} Z.plus(X, Y) where bool.and(Z.is(X), Z.is(Y)) ;

rule/simple [stmt-ite-true]:
	ite[B,X,Y] => X where B ;

rule/simple [stmt-ite-false]:
	ite[B,X,Y] => Y where bool.eq(B, bool.false) ;

rule [while-unfold]: while[B,X] => ite[B, seq[X, while[B, X]], unitValue[]] ;



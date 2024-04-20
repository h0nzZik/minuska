@frames: [
  simple(X): c[builtin.cseq [X,REST], STATE]
];
@value(X): (bool.or(z.is(X), term.same_symbol(X, [var[]]))) ;
@context(HOLE): c[HOLE];
@strictness: [
  plus of_arity 2 in [0,1],
  minus of_arity 2 in [0,1],
  assign of_arity 2 in [1]
];


@rule [init]: builtin.init[X] => c[builtin.cseq[X, builtin.empty_cseq[]], map.empty()] where bool.true();
@rule [finish]: c[builtin.cseq[X, builtin.empty_cseq[]]] => builtin.result[X] where z.is(X) ;

@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where bool.and(z.is(X), z.is(Y)) ;
@rule/simple [minus]: minus[X,Y] => z.minus(X, Y) where bool.and(z.is(X), z.is(Y)) ;

@rule [var.assign]: c[builtin.cseq[assign[X,V],REST], STATE] => c[builtin.cseq[unitValue[], REST], map.update(STATE, X, V)] where bool.and(term.same_symbol(X, [var[]]), z.is(V)) ;
@rule [var.lookup]: c[builtin.cseq[X, REST], STATE] => c[builtin.cseq[map.lookup(STATE, X), REST], STATE] where term.same_symbol(X, [var[]]) ;



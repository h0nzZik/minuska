@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
@value(X): (z.is(X)) ;
@context(HOLE): c[HOLE];
@strictness: [
  plus of_arity 2 in [0,1],
  minus of_arity 2 in [0,1]
];


@rule [init]: builtin.init[X] => c[builtin.cseq[X, builtin.empty_cseq[]]] where bool.true();
@rule [finish]: c[builtin.cseq[X, builtin.empty_cseq[]]] => builtin.result[X] where z.is(X) ;

@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where bool.and(z.is(X), z.is(Y)) ;
@rule/simple [minus]: minus[X,Y] => z.minus(X, Y) where bool.and(z.is(X), z.is(Y)) ;


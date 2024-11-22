@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
@value(X): (is_true(z.is(X))) ;
@nonvalue(X): (is_true(bool.neg(z.is(X)))) ;
@context(HOLE): c[HOLE];
@strictness: [
  plus of_arity 2 in [0,1],
  minus of_arity 2 in [0,1]
];


@rule [init]: builtin.init[X] => c[builtin.cseq[X, builtin.empty_cseq[]]] where [];
@rule [finish]: c[builtin.cseq[X, builtin.empty_cseq[]]] => builtin.result[X] where [is_true(z.is(X))] ;

@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where [is_true(z.is(X)), is_true(z.is(Y))] ;
@rule/simple [minus]: minus[X,Y] => z.minus(X, Y) where [is_true(z.is(X)), is_true(z.is(Y))] ;


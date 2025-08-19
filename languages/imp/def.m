@frames: [
  simple(X): c[builtin.cseq [X,REST], STATE]
];
@value(X): @or(z.is(X), @or(string.is(X), @or(bool.is(X), term.same_symbol(X, [unitValue[]]))));

@context(HOLE): c[HOLE, STATE];
@strictness: [
  plus of_arity 2 in [0,1],
  minus of_arity 2 in [0,1],
  assign of_arity 2 in [1],
  seq of_arity 2 in [0],
  ite of_arity 3 in [0],
  eq  of_arity 2 in [0,1],
  le  of_arity 2 in [0,1],
  lt  of_arity 2 in [0,1],
  neg of_arity 1 in [0]
];


@rule [init]: builtin.init[] => c[builtin.cseq[program.ast(), builtin.empty_cseq[]], map.empty()] where @true ;

@rule/simple [aexpr.plus]: plus[X,Y] => z.plus(X, Y) where @and(z.is(X), z.is(Y)) ;
@rule/simple [aexpr.minus]: minus[X,Y] => z.minus(X, Y) where @and(z.is(X), z.is(Y)) ;

@rule [var.assign]: c[builtin.cseq[assign[X,V],REST], STATE]
  => c[builtin.cseq[unitValue[], REST], map.update(STATE, X, V)]
   where @and(term.same_symbol(X, [var[]]), @or(z.is(V), string.is(V))) ;

@rule [var.lookup]: c[builtin.cseq[X, REST], STATE] => c[builtin.cseq[map.lookup(STATE, X), REST], STATE] where term.same_symbol(X, [var[]]) ;

@rule/simple [stmt.seq]: seq[unitValue[], X] => X where @true ;

@rule/simple [bexpr.eq]: eq[X, Y] => z.eq(X, Y) where @and(z.is(X), z.is(Y)) ;
@rule/simple [bexpr.le]: le[X, Y] => z.le(X, Y) where @and(z.is(X), z.is(Y)) ;
@rule/simple [bexpr.lt]: lt[X, Y] => z.lt(X, Y) where @and(z.is(X), z.is(Y)) ;
@rule/simple [bexpr.neg]: not[X] => bool.neg(X) where bool.is(X) ;

@rule/simple [stmt.ite.true]:  ite[B, X, Y] => X where @and(bool.is(B), bool.is_true(B)) ;
@rule/simple [stmt.ite.false]: ite[B, X, Y] => Y where @and(bool.is(B), bool.is_false(B)) ;

@rule/simple [while.unfold]: while[B, S] => ite[B, seq[S, while[B, S]], unitValue[]] where @true ;



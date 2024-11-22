@frames: [
  simple(X): c[builtin.cseq [X,REST], STATE]
];
@value(X): (is_true (bool.or(
   z.is(X),                            bool.or(
   bool.is(X),                         bool.or(
   term.same_symbol(X, [unitValue[]]), 
   string.is(X)
))))) ;
@nonvalue(X): (is_true (bool.neg(bool.or(
   z.is(X),                            bool.or(
   bool.is(X),                         bool.or(
   term.same_symbol(X, [unitValue[]]), 
   string.is(X)
)))))) ;
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


@rule [init]: builtin.init[X] => c[builtin.cseq[X, builtin.empty_cseq[]], map.empty()] where [];

@rule/simple [aexpr.plus]: plus[X,Y] => z.plus(X, Y) where [bool.and(z.is(X), z.is(Y))] ;
@rule/simple [aexpr.minus]: minus[X,Y] => z.minus(X, Y) where [bool.and(z.is(X), z.is(Y))] ;

@rule [var.assign]: c[builtin.cseq[assign[X,V],REST], STATE]
  => c[builtin.cseq[unitValue[], REST], map.update(STATE, X, V)]
   where [term.same_symbol(X, [var[]]), bool.or(z.is(V), string.is(V))] ;

@rule [var.lookup]: c[builtin.cseq[X, REST], STATE] => c[builtin.cseq[map.lookup(STATE, X), REST], STATE] where [term.same_symbol(X, [var[]])] ;

@rule/simple [stmt.seq]: seq[unitValue[], X] => X where [] ;

@rule/simple [bexpr.eq]: eq[X, Y] => z.eq(X, Y) where [z.is(X), z.is(Y)] ;
@rule/simple [bexpr.le]: le[X, Y] => z.le(X, Y) where [z.is(X), z.is(Y)] ;
@rule/simple [bexpr.lt]: lt[X, Y] => z.lt(X, Y) where [z.is(X), z.is(Y)] ;
@rule/simple [bexpr.neg]: not[X] => bool.neg(X) where [bool.is(X)] ;

@rule/simple [stmt.ite.true]: ite[B, X, Y] => X where [bool.is(B), bool.eq(B, bool.true())] ;
@rule/simple [stmt.ite.false]: ite[B, X, Y] => Y where [bool.is(B), bool.eq(B, bool.false())] ;

@rule/simple [while.unfold]: while[B, S] => ite[B, seq[S, while[B, S]], unitValue[]] where [] ;



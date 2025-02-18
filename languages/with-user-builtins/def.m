
@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
@value(X): @false ;
@context(HOLE): c[HOLE];
@strictness: [];

@rule [init]: builtin.init[] => c[builtin.cseq[program.ast(), builtin.empty_cseq[]], map.empty()] where @true;
@rule/simple [plus]: plus[X,Y] => z.plus(X, Y) where @and(z.is(X), z.is(Y)) ;

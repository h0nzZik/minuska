
@frames: [
  simple(X): c[builtin.cseq [X,REST]]
];
@value(X): @false ;
@context(HOLE): c[HOLE];
@strictness: [];

@rule [init]: builtin.init[] => c[builtin.cseq[program.ast(), builtin.empty_cseq[]], [(@builtin:int("5"))]] where @true;
@rule [step]: c[builtin.cseq[P, Rest], X] => c[builtin.cseq[P, Rest], z.plus(X, [(@builtin:int("1"))])] where z.is(X) ;

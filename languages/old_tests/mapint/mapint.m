@frames: [
];
@value(X): (bool.false()) ;
@context(HOLE): HOLE ;
@strictness: [];


@rule [init]: builtin.init[X] => a[map.empty()] where bool.true() ;
@rule [a]: a[M] => b[map.update(M, [(@builtin-int 1)], [(@builtin-int 2)])] where bool.true() ;
@rule [b]: b[M] => c[map.update(M, [(@builtin-int 2)], [(@builtin-int 3)])] where bool.true() ;
@rule [c]: c[M] => d[map.update(M, [(@builtin-int 3)], [(@builtin-int 4)])] where bool.true() ;
@rule [d]: d[M] => map.lookup(M, [(@builtin-int 1)]) where bool.true() ;



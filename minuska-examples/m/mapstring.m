@frames: [
];
@value(X): (bool.false()) ;
@context(HOLE): HOLE ;
@strictness: [];


@rule [init]: builtin.init[X] => a[map.empty()] where bool.true() ;
@rule [a]: a[M] => b[map.update(M, [(@builtin-string "g")], [(@builtin-string "goo")])] where bool.true() ;
@rule [b]: b[M] => c[map.update(M, [z[(@builtin-string "f")]], [(@builtin-string "foo")])] where bool.true() ;
@rule [c]: c[M] => d[map.update(M, [t[(@builtin-string "t")]], [(@builtin-string "too")])] where bool.true() ;
@rule [d]: d[M] => map.lookup(M, [z[(@builtin-string "f")]]) where bool.true() ;



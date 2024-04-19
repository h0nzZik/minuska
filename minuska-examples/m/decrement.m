@frames: [];
@value(X): (bool.false()) ;
@context(HOLE): u_cfg [ HOLE ];
@strictness: [];


@rule [init]: builtin.init[X] => X where bool.true() ;

@rule [decrement]: succ[X] => X where bool.true() ;




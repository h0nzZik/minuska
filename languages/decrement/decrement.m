@frames: [];
@value(X): (is_true(bool.false())) ;
@nonvalue(X): (is_true(bool.true())) ;
@context(HOLE): u_cfg [ HOLE ];
@strictness: [];


@rule [init]: builtin.init[X] => X where [] ;

@rule [decrement]: succ[X] => X where [] ;




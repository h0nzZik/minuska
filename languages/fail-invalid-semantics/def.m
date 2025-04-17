@frames: [];
@value(X): @false ;
@context(HOLE): u_cfg [ HOLE ];
@strictness: [];


@rule [init]: builtin.init[] => @query:program.ast() where @true ;

@rule [decrement]: succ[] => X where @true ;




@value(X): (bool.false()) ;

@strictness: [] ;

@frames: [
   fr1(X): u_cfg [ u_state [ u_cseq [ X, REST ], VALUES ] ]
];

@rule/fr1 [decrement]:
	succ[X] => X where bool.true()
    ;

@rule [decrement]:
	succ[X] => X where bool.true()
    ;




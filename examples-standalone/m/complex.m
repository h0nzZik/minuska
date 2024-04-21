@frames: [
   fr(X): u_cfg [ u_cseq [ X, REST ], VALUES ]
];

@value(X): (bool.false()) ;

@context(HOLE): u_cfg [ HOLE ];

@strictness: [
	if of_arity 3 in [0]
];


@rule/fr [if.true]: if[true[], T, F] => T where bool.true();
@rule/fr [if.false]: if[false[], T, F] => B where bool.true();

@rule [decrement]:
	succ[X] => X where bool.true()
    ;





From Minuska Require Import
    prelude
    spec
    string_variables
    builtins
    naive_interpreter
    default_static_model
    notations
    frontend
    interp_loop
.

Variant Act := default_act | invisible_act.


Module unary_nat.

    (* In this module we represent natural numbers using the unary encoding.
       In particular, we avoid using the built-in [Nat]s and [Z]s.
       (* We probably need to use built-in bools for side conditions, though. *)
    *)

    #[local]
    Instance Σ : StaticModel :=
        default_model (default_builtin.β)
    .
    
    Definition X : variable := "$X".
    Definition Y : variable := "$Y".
    Definition Tgt : variable := "$Tgt".
    Definition Curr : variable := "$Curr".
    Definition REST_SEQ : variable := "$REST_SEQ".

    (* Utilities *)
    Definition u_cseq_name : string := "u_cseq".
    Definition u_empty_cseq_name : string := "u_empty_cseq".

    Definition u_cfg {_br : BasicResolver} := (@t_term _ operand_type "u_cfg").
    Arguments u_cfg {_br} _%_rs.

    Definition u_cseq {_br : BasicResolver} := (@t_term _ operand_type u_cseq_name).
    Arguments u_cseq {_br} _%_rs.

    Definition u_emptyCseq {_br : BasicResolver} := (@t_term _ operand_type u_empty_cseq_name).
    Arguments u_emptyCseq {_br} _%_rs.


    (* Ctors *)
    Definition nat_succ {_br : BasicResolver} := (@t_term _ operand_type "nat_succ").
    Arguments nat_succ {_br} _%_rs.

    Definition nat_zero {_br : BasicResolver} := (@t_term _ operand_type "nat_zero").
    Arguments nat_zero {_br} _%_rs.

    Definition isValue :=  fun x =>
          ((isAppliedSymbol "nat_zero" x) || (isAppliedSymbol "nat_succ" x))%rs.

    #[local]
    Instance ImpDefaults : Defaults := {|
        default_cseq_name := u_cseq_name ;
        default_empty_cseq_name := u_empty_cseq_name ;
        default_context_template
            := (context-template u_cfg ([ HOLE ]) with HOLE) ;

        default_isValue := isValue ;
    |}.

    (* Operations *)
    Definition nat_add {_br : BasicResolver} := (@t_term _ operand_type "nat_add").
    Arguments nat_add {_br} _%_rs.

    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'where' c" := (
        decl_rule (rule [ s ]:
            u_cfg [ u_cseq [ l; t_over ($REST_SEQ) ] ]
         ~>{default_act} u_cfg [ u_cseq [ r; t_over ($REST_SEQ) ] ]
         where c
        )
    ) (at level 90).

    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'always'" := (
        decl_rule (rule [ s ]:
            u_cfg [ u_cseq [ l; t_over ($REST_SEQ) ] ]
         ~>{default_act} u_cfg [ u_cseq [ r; t_over ($REST_SEQ) ] ]
        )
    ) (at level 90).

    Definition Decls_nat_add : list Declaration := [
        decl_strict (symbol "nat_add" of arity 2 strict in [0;1]);
        decl_simple_rule ["nat-add-0"]:
            nat_add [nat_zero []; t_over ($Y) ] ~> t_over ($Y)
            always
        ;

        decl_simple_rule ["nat-add-S"]:
            nat_add [nat_succ [ t_over ($X) ]; t_over ($Y) ]
            ~> nat_add [t_over ($X); nat_succ [t_over ($Y)] ]
            always
        
    ].

    Definition nat_sub {_br : BasicResolver} := (@t_term _ operand_type "nat_sub").
    Arguments nat_sub {_br} _%_rs.

    Definition Decls_nat_sub : list Declaration := [
        decl_strict (symbol "nat_sub" of arity 2 strict in [0;1]);
        
        decl_simple_rule ["nat-sub-0"]:
            nat_sub [t_over ($X); nat_zero [] ]
            ~> t_over ($X)
            where (isValue ($X))
        ;
        decl_simple_rule ["nat-sub-S"]:
            nat_add [ nat_succ [ t_over ($X) ]; nat_succ [ t_over ($Y) ] ]
            ~> nat_add [t_over ($X); t_over ($Y) ]
            always
    ].

    Definition nat_mul {_br : BasicResolver} := (@t_term _ operand_type "nat_mul").
    Arguments nat_mul {_br} _%_rs.

    (* depends on: Decls_nat_add *)
    Definition Decls_nat_mul : list Declaration := [
        decl_strict (symbol "nat_mul" of arity 2 strict in [0;1]);
        decl_simple_rule ["nat-mul-0"]:
            nat_mul [nat_zero []; t_over ($Y) ]
            ~> nat_zero []
            where (isValue ($Y))
        ;
        
        decl_simple_rule ["nat-mul-S"]:
            nat_mul [ nat_succ [ t_over ($X) ]; t_over ($Y) ]
            ~> nat_add [t_over ($Y); nat_mul[ t_over ($X); t_over ($Y)] ]
                where (isValue ($Y))
    ].


    Definition nat_fact {_br : BasicResolver} := (@t_term _ operand_type "nat_fact").
    Arguments nat_fact {_br} _%_rs.

    Definition nat_fact' {_br : BasicResolver} := (@t_term _ operand_type "nat_fact'").
    Arguments nat_fact' {_br} _%_rs.

    (* depends on: Decls_nat_mul *)
    Definition Decls_nat_fact : list Declaration := [
        (* decl_strict (symbol "nat_fact" of arity 1 strict in [0]); *)
        decl_strict (symbol "nat_fact'" of arity 2 strict in [0;1]);
        
        decl_simple_rule ["nat-fact"]:
            nat_fact [ t_over ($X) ]
            ~> nat_fact' [ t_over ($X); nat_succ [nat_zero []] ]
            where (isValue ($X))
        ;
        
        decl_simple_rule ["nat-fact'-0"]:
            nat_fact' [ nat_zero []; t_over ($Y) ]
            ~> t_over ($Y)
            where (isValue ($Y))
        ;
        decl_simple_rule ["nat-fact'-S"]:
            nat_fact' [ nat_succ [ t_over ($X) ]; t_over ($Y) ]
            ~> nat_fact' [ t_over ($X); nat_mul [ nat_succ [ t_over ($X) ]; t_over ($Y) ]  ]
            where (isValue ($Y))
    ].

    Definition Γfact : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act (Decls_nat_fact ++ Decls_nat_mul ++ Decls_nat_add))).

    Definition initial_expr (x : TermOver builtin_value) :=
        (ground (
            u_cfg [ u_cseq [x; u_emptyCseq [] ] ]
        ))
    .

    Fixpoint nat_to_unary (n : nat) : TermOver builtin_value :=
    match n with
    | 0 => (ground (nat_zero []))
    | S n' => (ground (nat_succ [ nat_to_unary n' ]))
    end.

    Fixpoint unary_to_nat
        (g : TermOver builtin_value) : option nat :=
    match g with
    | t_term "nat_zero" nil => Some 0
    | t_term "nat_succ" [g'] => n ← (unary_to_nat g'); Some (S n)
    | _ => None
    end
    .

    Definition initial_fact (n : nat) := initial_expr (
        (ground (nat_fact [(nat_to_unary n)]))
    ).

    Definition final (g : TermOver builtin_value) : option nat :=
    match g with
    | t_term "u_cfg" [t_term "u_cseq" [val; _]] => (unary_to_nat val)
    | _ => None
    end
    .

    Definition interp_fact(fuel : nat) (from : nat)
    := let r := interp_loop (tl _ nondet_stream) (naive_interpreter Γfact.1) fuel (initial_fact from) in
        (r.1, (final r.2))
    .
    (* Time Compute ((interp_fact 500 4)). *)
    (*
    Lemma interp_fact_5:
            ((interp_fact 500 4)) = (377, Some 24)
    .
    Proof. reflexivity. Qed.
    *)

    Definition nat_fib {_br : BasicResolver} := (@t_term _ operand_type "nat_fib").
    Arguments nat_fib {_br} _%_rs.

    Definition nat_fib' {_br : BasicResolver} := (@t_term _ operand_type "nat_fib'").
    Arguments nat_fib' {_br} _%_rs.

    Definition Decls_nat_fib : list Declaration := [
        decl_simple_rule ["just-0"]:
            nat_fib [ nat_zero [] ]
            ~> nat_zero []
            always
        ;
        decl_simple_rule ["just-1"]:
            nat_fib [ nat_succ [nat_zero []] ]
            ~> nat_succ [nat_zero []]
            always
        ;
        decl_strict (symbol "nat_fib'" of arity 4 strict in [2]); (* TODO *)
        
        decl_simple_rule ["two-or-more"]:
            nat_fib [ nat_succ [nat_succ [ t_over ($X) ] ] ]
            ~> nat_fib' [
                nat_succ [nat_succ [ t_over ($X) ] ];
                nat_succ [nat_succ [ nat_zero [] ] ];
                nat_succ [ nat_zero [] ];
                nat_succ [ nat_zero [] ] 
            ]
            always
        ;
        
        decl_simple_rule ["step"]:
            nat_fib' [ t_over ($Tgt); t_over ($Curr); t_over ($X); t_over ($Y) ]
            ~> nat_fib' [ t_over ($Tgt); nat_succ [ t_over ($Curr) ]; nat_add [t_over ($X); t_over ($Y)]; t_over ($X) ]
            where (~~ ($Curr ==Gen $Tgt))
        ;
        
        decl_simple_rule ["result"]:
            nat_fib' [ t_over ($Tgt); t_over ($Tgt); t_over ($X); t_over ($Y) ]
            ~> t_over ($X)
            always
    ].

    Definition Γfib : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act (Decls_nat_fib ++ Decls_nat_add))).

    Definition initial_fib (n : nat) := initial_expr (
        (ground (nat_fib [(nat_to_unary n)]))
    ).

    Definition interp_fib (fuel : nat) (from : nat)
    := 
        let r := interp_loop (tl _ nondet_stream) (naive_interpreter Γfib.1) fuel ((initial_fib from)) in
        (r.1, (final r.2))
    .

    (* Compute (interp_fib 5000 11). *)
    (*
    Lemma interp_test_fib_11: (interp_fib 5000 11) = (4359, Some 89)
    .
    Proof. reflexivity. Qed.
    *)

End unary_nat.
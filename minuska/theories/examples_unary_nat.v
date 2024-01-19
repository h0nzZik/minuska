
From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    builtins
    flattened
    naive_interpreter
    default_static_model
    notations
    frontend
    interp_loop
.

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
    Definition REST_SEQ : variable := "$REST_SEQ".

    (* Utilities *)
    Definition u_cseq_name : string := "u_cseq".
    Definition u_empty_cseq_name : string := "u_empty_cseq".

    Definition u_cfg {_br : BasicResolver} := (apply_symbol "u_cfg").
    Arguments u_cfg {_br} _%rs.

    Definition u_cseq {_br : BasicResolver} := (apply_symbol u_cseq_name).
    Arguments u_cseq {_br} _%rs.

    Definition u_emptyCseq {_br : BasicResolver} := (apply_symbol u_empty_cseq_name).
    Arguments u_emptyCseq {_br} _%rs.


    (* Ctors *)
    Definition nat_succ {_br : BasicResolver} := (apply_symbol "nat_succ").
    Arguments nat_succ {_br} _%rs.

    Definition nat_zero {_br : BasicResolver} := (apply_symbol "nat_zero").
    Arguments nat_zero {_br} _%rs.

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
    Definition nat_add {_br : BasicResolver} := (apply_symbol "nat_add").
    Arguments nat_add {_br} _%rs.

    Notation "'simple_rule' '[' s ']:' l '~>' r 'where' c" := (
        rule [ s ]:
            u_cfg [ u_cseq [ l, $REST_SEQ ] ]
         ~> u_cfg [ u_cseq [ r, $REST_SEQ ] ]
         where c
    ) (at level 90).

    Notation "'simple_rule' '[' s ']:' l '~>' r 'always'" := (
        rule [ s ]:
            u_cfg [ u_cseq [ l, $REST_SEQ ] ]
         ~> u_cfg [ u_cseq [ r, $REST_SEQ ] ]
    ) (at level 90).

    Definition Decls_nat_add : list Declaration := [
        decl_strict (symbol "nat_add" of arity 2 strict in [0;1]);
        decl_rule (
            simple_rule ["nat-add-0"]:
                nat_add [nat_zero [], ($Y) ]
                ~> $Y
            always
        );
        decl_rule (
            simple_rule ["nat-add-S"]:
                nat_add [nat_succ [ $X ], ($Y) ]
                ~> nat_add [$X, nat_succ [$Y] ]
            always
        )
    ].

    Definition nat_sub {_br : BasicResolver} := (apply_symbol "nat_sub").
    Arguments nat_sub {_br} _%rs.

    Definition Decls_nat_sub : list Declaration := [
        decl_strict (symbol "nat_sub" of arity 2 strict in [0;1]);
        decl_rule (
            simple_rule ["nat-sub-0"]:
                nat_sub [$X, nat_zero [] ]
                ~> $X
                where (isValue ($X))
        );
        decl_rule (
            simple_rule ["nat-sub-S"]:
                nat_add [ nat_succ [ $X ], nat_succ [ $Y ] ]
                ~> nat_add [$X, $Y ]
            always
        )
    ].

    Definition nat_mul {_br : BasicResolver} := (apply_symbol "nat_mul").
    Arguments nat_mul {_br} _%rs.

    (* depends on: Decls_nat_add *)
    Definition Decls_nat_mul : list Declaration := [
        decl_strict (symbol "nat_mul" of arity 2 strict in [0;1]);
        decl_rule (
            simple_rule ["nat-mul-0"]:
                nat_mul [nat_zero [], $Y ]
                ~> nat_zero []
                where (isValue ($Y))
        );
        decl_rule (
            simple_rule ["nat-mul-S"]:
                nat_mul [ nat_succ [ $X ], $Y ]
                ~> nat_add [$Y, nat_mul[ $X, $Y] ]
                where (isValue ($Y))
        )
    ].


    Definition nat_fact {_br : BasicResolver} := (apply_symbol "nat_fact").
    Arguments nat_fact {_br} _%rs.

    Definition nat_fact' {_br : BasicResolver} := (apply_symbol "nat_fact'").
    Arguments nat_fact' {_br} _%rs.

    (* depends on: Decls_nat_mul *)
    Definition Decls_nat_fact : list Declaration := [
        decl_strict (symbol "nat_fact" of arity 1 strict in [0]);
        decl_strict (symbol "nat_fact'" of arity 2 strict in [0;1]);
        decl_rule (
            simple_rule ["nat-fact"]:
                nat_fact [ $X ]
                ~> nat_fact' [ $X, nat_succ [nat_zero []] ]
                where (isValue ($X))
        );
        decl_rule (
            simple_rule ["nat-fact'-0"]:
                nat_fact' [ nat_zero [], $Y ]
                ~> $Y
                where (isValue ($Y))
        );
        decl_rule (
            simple_rule ["nat-fact'-S"]:
                nat_fact' [ nat_succ [ $X ], $Y ]
                ~> nat_fact' [ $X, nat_mul [ nat_succ [ $X ], $Y ]  ]
                where (isValue ($Y))
        )
    ].

    Definition Γfact : FlattenedRewritingTheory*(list string) := Eval vm_compute in 
    (to_theory (process_declarations (Decls_nat_fact ++ Decls_nat_mul ++ Decls_nat_add))).

    Definition initial_expr (x : AppliedOperatorOr' symbol builtin_value) :=
        (ground (
            u_cfg [ u_cseq [x, u_emptyCseq [] ] ]
        ))
    .

    Fixpoint nat_to_unary (n : nat) : GroundTerm :=
    match n with
    | 0 => (ground (nat_zero []))
    | S n' => (ground (nat_succ [ nat_to_unary n' ]))
    end.

    Fixpoint unary_to_nat'
        (g : AppliedOperator' symbol builtin_value) : option nat :=
    match g with
    | ao_operator "nat_zero" => Some 0
    | ao_app_ao (ao_operator "nat_succ") g' => n ← (unary_to_nat' g'); Some (S n)
    | _ => None
    end
    .

    Definition unary_to_nat (g : GroundTerm) : option nat :=
    match g with
    | aoo_app ao => unary_to_nat' ao
    | aoo_operand _ => None
    end
    .

    Definition initial_fact (n : nat) := initial_expr (
        (ground (nat_fact [(nat_to_unary n)]))
    ).

    Definition fact_final (g : GroundTerm) : option nat :=
    match g with
    |  aoo_app 
        (ao_app_ao 
            (ao_operator "u_cfg")
            (ao_app_ao 
                (ao_app_ao 
                    (ao_operator "u_cseq")
                    val
                )
                _
            )
        ) => (unary_to_nat' val)
    | _ => None
    end
    .

    Definition interp_fact(fuel : nat) (from : nat)
    := let r := interp_in_from Γfact fuel (initial_fact from) in
        (r.1.1, (fact_final r.1.2), r.2)
    .

    Lemma interp_fact_5:
        exists (rem:nat),
            ((interp_fact 500 4).1) = (rem, Some 24)
    .
    Proof.
        eexists. reflexivity.
    Qed.

    Time Compute ((interp_fact 5000 6).1).

End unary_nat.
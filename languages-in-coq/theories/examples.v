From Coq.Logic Require Import ProofIrrelevance.
From stdpp Require Import countable.

From Minuska Require Import
    prelude
    spec
    basic_properties
    string_variables
    builtins
    spec_interpreter
    naive_interpreter
    interpreter_results
    default_static_model
    notations
    frontend
    interp_loop
    example
    pval_ocaml_binding
.

From Minuska Require Import
    builtin.klike
    pi.trivial
.
Import builtin.klike.Notations.

Definition mybeta := (bi_beta MyUnit builtins_klike).
Existing Instance mybeta.

Definition mypi := pi.trivial.MyProgramInfo.
#[local]
Existing Instance mypi.


Variant Act := default_act | invisible_act.

#[global]
Instance Act_eqDec : EqDecision Act.
Proof.
    ltac1:(solve_decision).
Defined.

Module two_counters.

    #[local]
    Instance Σ : StaticModel := default_model (mybeta) mypi.

    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "S").
    Arguments s {_br} _%_rs.

    Definition Γ : (RewritingTheory2 Act)*(list string) :=
    Eval vm_compute in (to_theory Act (process_declarations Act default_act _ mypi ([
        decl_rule (
            rule ["my-rule"]:
                cfg [ state [ s [ t_over ($M) ]; t_over ($N) ] ]
            ~>{default_act} cfg [ state [ t_over ($M); s [ t_over ($N) ]  ] ]
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : nat*nat) : (TermOver builtin_value) :=
        t_term "cfg" [(t_term "state" [(example.example_1.my_number' mn.1);(example.example_1.my_number' mn.2)])]
    .

    Definition state_to_pair (g : (TermOver builtin_value)) : option (nat*nat) :=
    match g with
    | t_term s1 [(t_term s2 [(m');(n')])] =>
            if (decide (s1 = "cfg" /\ s2 = "state")) then
                m ← example_1.my_number'_inv m';
                n ← example_1.my_number'_inv n';
                Some (m, n)
            else None
    | _ => None
    end
    .

    Lemma pair_state_inversion : forall m n,
        state_to_pair (pair_to_state (m,n)) = Some (m,n)
    .
    Proof.
        intros m n.
        simpl.
        rewrite bind_Some.
        exists m.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        rewrite bind_Some.
        exists n.
        split.
        { rewrite example_1.my_number_inversion'. reflexivity. }
        reflexivity.
    Qed.

    Definition interp_loop_number fuel := 
        fun (m n : nat) =>
        let fg' := ((interp_loop nondet_gen 0 (interp (t_over bv_error)) fuel) ∘ pair_to_state) (m,n) in
        state_to_pair fg'.2
    .
    Compute (interp_loop_number 100 10 10).
    (*Print Transparent Dependencies interp_loop_number.*)
    (* Print Opaque Dependencies interp_loop_number. *)
    
    Lemma iln_100_10_10:
        (interp_loop_number 100 10 10) = Some (0, 20)
    .
    Proof.
        reflexivity.
    Qed.
    (* Time Compute (interp_loop_number 10000000 10000 10000). *)

End two_counters.

Module two_counters_Z.
#[local]
    Instance Σ : StaticModel := default_model (mybeta) mypi.

    Definition M : variable := "M".
    Definition N : variable := "N".
    
    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    (* Coercion Z_to_builtin (x : Z) := (e_ground (t_over (bv_Z x))). *)

    Definition Γ : (RewritingTheory2 Act)*(list string) :=
    Eval vm_compute in (to_theory Act (process_declarations Act default_act _ mypi ([
        decl_rule (
            rule ["my-rule"]:
               state [ t_over ($M) ; t_over ($N) ]
            ~>{default_act} state [
                t_over ((($M)) -Z (e_ground (t_over (bv_Z 1%Z))));
                t_over (($N) +Z (($M)))
                ]
            where [mkSideCondition2 _ b_cond_is_true [($M >Z (e_ground (t_over (bv_Z 0%Z))))]]
        )
    ]))).
    

    Definition interp :=
        naive_interpreter Γ.1
    .

    Definition pair_to_state (mn : (Z * Z)%type) : (TermOver builtin_value) :=
        (ground(
            t_term "state" [t_over (bv_Z mn.1); t_over (bv_Z mn.2)]
        ))
    .

    Definition state_to_pair (g : (TermOver builtin_value)) : option (Z * Z) :=
    match g with
    | t_term "state" [t_over (bv_Z m); t_over (bv_Z n)] =>
            Some (m, n)
    | _ => None
    end
    .

    Definition interp_loop_number (fuel : nat) := 
        fun (m n : Z) =>
        let fg' := (((interp_in_from (t_over bv_error) Γ nondet_gen fuel)) ∘ pair_to_state) (m,n) in
        state_to_pair fg'.1.2
    .

End two_counters_Z.

(* Check "End two counters". *)
Module arith.

    #[local]
    Instance Σ : StaticModel := default_model (mybeta) mypi.

    Definition X : variable := "X".
    Definition Y : variable := "Y".
    Definition REST_SEQ : variable := "$REST_SEQ".
    
    Definition u_cseq {_br : BasicResolver} := (@t_term _ operand_type "cseq").
    Arguments u_cseq {_br} _%_rs.

    Definition u_emptyCseq {_br : BasicResolver} := (@t_term _ operand_type "emptyCseq").
    Arguments u_emptyCseq {_br} _%_rs.

    Definition plus {_br : BasicResolver} := (@t_term _ operand_type "plus").
    Arguments plus {_br} _%_rs.

    Definition minus {_br : BasicResolver} := (@t_term _ operand_type "minus").
    Arguments minus {_br} _%_rs.

    Definition times {_br : BasicResolver} := (@t_term _ operand_type "times").
    Arguments times {_br} _%_rs.

    Definition div {_br : BasicResolver} := (@t_term _ operand_type "div").
    Arguments div {_br} _%_rs.

    Definition cfg {_br : BasicResolver} := (@t_term _ operand_type "cfg").
    Arguments cfg {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition s {_br : BasicResolver} := (@t_term _ operand_type "S").
    Arguments s {_br} _%_rs.

    Definition freezer {_br : BasicResolver} (sym : symbol) (position : nat)
    :=
        (@t_term _ operand_type ("freezer_" +:+ sym +:+ "_" +:+ (pretty position)))
    .
    Arguments freezer {_br} _%_rs.


    Declare Scope LangArithScope.
    Delimit Scope LangArithScope with larith.

    Notation "x '+' y" := (plus [ x; y ])%larith.
    Notation "x '-' y" := (minus [ x; y ])%larith.
    Notation "x '*' y" := (times [ x; y ])%larith.
    Notation "x '/' y" := (div [ x; y ])%larith.

    Open Scope larith.

    #[local]
    Instance ArithDefaults : Defaults := {|
        default_cseq_name := "cseq" ;
        default_empty_cseq_name := "emptyCseq" ;
        default_context_template
            := (context-template cfg [ HOLE ] with HOLE) ;

        default_isValue := fun x => mkSideCondition2 _ b_cond_is_true [(isZ x)] ;
        default_isNonValue := fun x => mkSideCondition2 _ b_cond_is_true [e_fun b_bool_neg [(isZ x)]] ;
        
    |}.

    Definition Decls : list Declaration := [
        (* plus *)
        decl_rule (
            rule ["plus-nat-nat"]:
                cfg [ u_cseq [ (t_over ($X) + t_over ($Y) ); t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X +Z $Y) ; t_over ($REST_SEQ) ] ]
                where [mkSideCondition2 _ b_cond_is_true [(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )]]
        );
        decl_strict (symbol "plus" of arity 2 strict in [0;1]);
        (* minus *)
        decl_rule (
            rule ["minus-nat-nat"]:
                cfg [ u_cseq [ (t_over ($X) - t_over ($Y)); t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X -Z $Y) ; t_over ($REST_SEQ) ] ]
                where [mkSideCondition2 _ b_cond_is_true [(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )]]
        );
        decl_strict (symbol "minus" of arity 2 strict in [0;1]);
        (* times *)
        decl_rule (
            rule ["times-nat-nat"]:
                cfg [ u_cseq [ (t_over ($X) * t_over ($Y)); t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X *Z $Y) ; t_over ($REST_SEQ) ] ]
                where [mkSideCondition2 _ b_cond_is_true [(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                    )]]
        );
        decl_strict (symbol "times" of arity 2 strict in [0;1]);
        (* div *)
        decl_rule (
            rule ["div-nat-nat"]:
                cfg [ u_cseq [ (t_over ($X) / t_over ($Y)); t_over ($REST_SEQ) ] ]
            ~>{default_act} cfg [ u_cseq [ t_over ($X /Z $Y) ; t_over ($REST_SEQ) ] ]
                where [mkSideCondition2 _ b_cond_is_true [(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )]]
        );
        decl_strict (symbol "div" of arity 2 strict in [0;1])
    ].

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act _ mypi (Decls))).


    (*
    Definition initial1 (x y : nat) :=
        (ground (cfg [ u_cseq [ ((@term_operand symbol _ (bv_Z x)) + (@term_operand symbol _ (bv_Z y))), u_emptyCseq [] ] ]))
    .*)

    Definition initial0 (x : TermOver builtin_value) :=
        (ground (
            cfg [
                u_cseq [ 
                    x;
                    u_emptyCseq []
                    ]
                ]
            )
        )
    .

    Definition initial (x: Z) (ly : list Z) :=
        (ground (initial0 ((foldr 
            (fun a (b : TermOver builtin_value) =>
                plus [(t_over (bv_Z a)) ; b]
            )
            (t_over (bv_Z x))
            ly
        ))))
    .

    Definition interp_from (fuel : nat) from
        := interp_in_from (t_over bv_error) Γ nondet_gen fuel from
    .

    Definition interp_list (fuel : nat) (x : Z) (ly : list Z)
    :=
        interp_from fuel (initial x ly)
    .

    
    Lemma interp_list_test_1:
        exists log,
        (interp_list 20 1 [20%Z;30%Z;40%Z]) = (12, (initial 91 nil), log)
    .
    Proof. eexists. reflexivity. Qed.

    (*
    Eval vm_compute in (interp_from 10 (ground (initial0
    (
        (t_over (bv_Z 3) + t_over (bv_Z 4)) + (t_over (bv_Z 5) + t_over (bv_Z 6))
    )))).
    *)
    Lemma interp_test_2:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    (t_over (bv_Z 3) + t_over (bv_Z 4))
                    +
                    (t_over (bv_Z 5) + t_over (bv_Z 6))
                ))))
            = (rem, (ground (initial0 ((t_over  (bv_Z 18))))), log)
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.


    Lemma interp_test_3:
        exists rem log,
            (interp_from 10 (ground (initial0
                (
                    (t_over (bv_Z 5) * t_over (bv_Z 6))
                    /
                    (t_over (bv_Z 3) + t_over (bv_Z 4))
                    
                ))))
            = (rem, (ground (initial0 (t_over (bv_Z 4)))), log)
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

End arith.

Check "End arith".

Module fib_native.

    #[local]
    Instance Σ : StaticModel := default_model (mybeta) mypi.

    Check builtin_value.

    Definition X : variable := "X".
    Definition Y : variable := "Y".
    Definition Curr : variable := "Curr".
    Definition Tgt : variable := "Tgt".
    Definition REST_SEQ : variable := "$REST_SEQ".
    
    Definition initialState {_br : BasicResolver} := (@t_term _ operand_type "initialState").
    Arguments initialState {_br} _%_rs.

    Definition resultState {_br : BasicResolver} := (@t_term _ operand_type "resultState").
    Arguments resultState {_br} _%_rs.

    Definition state {_br : BasicResolver} := (@t_term _ operand_type "state").
    Arguments state {_br} _%_rs.

    Definition Decls : list Declaration := [
        decl_rule (
            rule ["just-0"]:
               initialState [ t_over  (bov_builtin (bv_Z 0)) ]
            ~>{default_act} resultState [ t_over  (e_ground (t_over (bv_Z 0))) ]
        );
        decl_rule (
            rule ["just-1"]:
               initialState [ t_over (bov_builtin (bv_Z 1)) ]
            ~>{default_act} resultState [ t_over  (e_ground (t_over  (bv_Z 1))) ]
        );
        decl_rule (
            rule ["two-or-more"]:
               initialState [ t_over  ($Tgt) ]
            ~>{default_act} state [
                t_over ($Tgt);
                t_over (e_ground (t_over  (bv_Z 2)));
                t_over (e_ground (t_over  (bv_Z 1)));
                t_over (e_ground (t_over  (bv_Z 1))) 
               ]
            where [mkSideCondition2 _ b_cond_is_true [((~~ ($Tgt ==Z (e_ground (t_over (bv_Z 0)))))
                && (~~ ($Tgt ==Z (e_ground (t_over (bv_Z 1))))))]]
        );
        decl_rule (
            rule ["step"]:
               state [ t_over ($Tgt); t_over  ($Curr); t_over ($X); t_over ($Y) ]
            ~>{default_act} state [ t_over ($Tgt); t_over (($Curr) +Z (e_ground (t_over  (bv_Z 1)))); t_over ($X +Z $Y); t_over ($X) ]
            where [mkSideCondition2 _ b_cond_is_true [(~~ ((($Curr)) ==Z (($Tgt))))]]
        );
        decl_rule (
            rule ["result"]:
               state [ t_over ($Tgt); t_over ($Curr); t_over ($X); t_over ($Y) ]
            ~>{default_act} resultState [ t_over ($X) ]
                where [mkSideCondition2 _ b_cond_is_true [(($Curr ==Z $Tgt))]]
        )
    ].

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act _ mypi (Decls))).


    Definition interp_from (fuel : nat) from
        := interp_in_from (t_over bv_error) Γ nondet_gen fuel from
    .

    Definition initial0 (x : TermOver builtin_value) :=
        (ground (
            initialState [ x ]
        ))
    .

    Definition fib_interp_from (fuel : nat) (from : Z)
        := interp_in_from (t_over bv_error) Γ nondet_gen fuel (ground (initial0
                (t_over (bv_Z from))))
    .

    Definition fib_interp_from_toint
        (fuel : nat) (from : Z)
    :=
        let r := fib_interp_from fuel from in
        let n : Z := (match r.1.2 with
          t_term "resultState" [t_over (bv_Z val)]
          => val
        | _ => Z0
        end) in
        (r.1.1,n,r.2)
    .

    
    (*
    Eval vm_compute in (interp_from 50 (ground (initial0
    (
        (t_over (bv_Z 7))
    )))).
    *)

    (*
    Compute (fib_interp_from 10 2).
    Eval simpl in (fib_interp_from 10 2).
    Eval cbv in (fib_interp_from 10 2). *)

    
    Lemma interp_test_fib_0:
        exists rem log,
            (fib_interp_from 10 0)
            = (rem, (ground (resultState [(t_over (bv_Z 0))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_1:
        exists rem log,
            (fib_interp_from 10 1)
            = (rem, (ground (resultState [(t_over  (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

   
    (* This is just a test that equality of terms is reducible *)
    Definition my_flag : bool := Eval vm_compute in
        bool_decide (
            (@t_term symbol builtin_value "state" [t_over (bv_Z 2); t_over (bv_Z 2); t_over (bv_Z 1); t_over (bv_Z 1)])
            = (@t_term symbol builtin_value "state" [t_over (bv_Z 2); t_over (bv_Z 2); t_over (bv_Z 1); t_over (bv_Z 2)])
        )
    .

    About false.
    Lemma test_of_computational_behavior:
        my_flag = Coq.Init.Datatypes.false
    .
    Proof. reflexivity. Qed.

    Compute (interp_from 1 (t_term "state"
          [t_over (bv_Z 2); t_over (bv_Z 2); t_over (bv_Z 1); t_over (bv_Z 1)])).
    
    Compute (fib_interp_from 2 2).

    Compute (fib_interp_from 10 2).

    Lemma interp_test_fib_2:
        exists rem log,
            (fib_interp_from 10 2)
            = (rem, (ground (resultState [(t_over  (bv_Z 1))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.

    Lemma interp_test_fib_3:
        exists rem log,
            (fib_interp_from 10 3)
            = (rem, (ground (resultState [(t_over  (bv_Z 2))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.


    Lemma interp_test_fib_11:
        exists rem log,
            (fib_interp_from 20 11)
            = (rem, (ground (resultState [(t_over (bv_Z 89))])), log)
    .
    Proof. eexists. eexists. reflexivity. Qed.
    
End fib_native.

Module imp.

    #[local]
    Instance Σ : StaticModel := default_model (mybeta) mypi.


    Definition B : variable := "$B".
    Definition X : variable := "$X".
    Definition Y : variable := "$Y".
    Definition VALUES : variable := "$VALUES".
    Definition REST_SEQ : variable := "$REST_SEQ".

    Definition var {_br : BasicResolver} := (@t_term _ operand_type "var").
    Arguments var {_br} _%_rs.

    (* Utilities *)
    Definition u_cseq_name : string := "u_cseq".
    Definition u_empty_cseq_name : string := "u_empty_cseq".

    Definition u_cseq {_br : BasicResolver} := (@t_term _ operand_type u_cseq_name).
    Arguments u_cseq {_br} _%_rs.

    Definition u_emptyCseq {_br : BasicResolver} := (@t_term _ operand_type u_empty_cseq_name).
    Arguments u_emptyCseq {_br} _%_rs.

    Definition u_cfg {_br : BasicResolver} := (@t_term _ operand_type "u_cfg").
    Arguments u_cfg {_br} _%_rs.

    Definition u_state {_br : BasicResolver} := (@t_term _ operand_type "u_state").
    Arguments u_state {_br} _%_rs.

    (* Data *)
    Definition unitValue {_br : BasicResolver} := (@t_term _ operand_type "unitValue").
    Arguments unitValue {_br} _%_rs.


    (* Arithmetics *)
    Definition arith_plus {_br : BasicResolver} := (@t_term _ operand_type "arith_plus").
    Arguments arith_plus {_br} _%_rs.

    Definition arith_minus {_br : BasicResolver} := (@t_term _ operand_type "arith_minus").
    Arguments arith_minus {_br} _%_rs.

    Definition arith_times {_br : BasicResolver} := (@t_term _ operand_type "arith_times").
    Arguments arith_times {_br} _%_rs.

    Definition arith_div {_br : BasicResolver} := (@t_term _ operand_type "arith_div").
    Arguments arith_div {_br} _%_rs.

    (* Boolean expressions *)

    Definition bexpr_lt {_br : BasicResolver} := (@t_term _ operand_type "bexpr_lt").
    Arguments bexpr_lt {_br} _%_rs.

    Definition bexpr_le {_br : BasicResolver} := (@t_term _ operand_type "bexpr_le").
    Arguments bexpr_le {_br} _%_rs.

    Definition bexpr_eq {_br : BasicResolver} := (@t_term _ operand_type "bexpr_eq").
    Arguments bexpr_eq {_br} _%_rs.

    Definition bexpr_negb {_br : BasicResolver} := (@t_term _ operand_type "bexpr_negb").
    Arguments bexpr_negb {_br} _%_rs.

    (* Statements *)
    Definition stmt_assign {_br : BasicResolver} := (@t_term _ operand_type "stmt_assign").
    Arguments stmt_assign {_br} _%_rs.

    Definition stmt_seq {_br : BasicResolver} := (@t_term _ operand_type "stmt_seq").
    Arguments stmt_seq {_br} _%_rs.

    Definition stmt_ite {_br : BasicResolver} := (@t_term _ operand_type "stmt_ite").
    Arguments stmt_ite {_br} _%_rs.

    Definition stmt_while {_br : BasicResolver} := (@t_term _ operand_type "stmt_while").
    Arguments stmt_while {_br} _%_rs.

    Declare Scope LangImpScope.
    Delimit Scope LangImpScope with limp.
    Close Scope LangImpScope.

    Notation "x '+' y" := (arith_plus [ x; y ]) : LangImpScope.
    Notation "x '-' y" := (arith_minus [ x; y ]) : LangImpScope.
    Notation "x '*' y" := (arith_times [ x; y ]) : LangImpScope.
    Notation "x '/' y" := (arith_div [ x; y ]) : LangImpScope.

    Check @t_over.
    Definition builtin_string (s : string) := ((@t_over (@symbol Σ) builtin_value (bv_str s))).

    Notation "x '<=' y" := (bexpr_le [x; y]) (at level 70) : LangImpScope.

    Notation "x '<:=' y" := (stmt_assign [x; y]) (at level 90) : LangImpScope.
    Notation "c ';' 'then' d" := (stmt_seq [c; d]) (at level 90, right associativity) : LangImpScope.
    Notation "'if' c 'then' x 'else' y "
        := (stmt_ite [c; x; y])
            (at level 200, c at level 200, x at level 200, y at level 200)
            : LangImpScope.


    Notation "'while' c 'do' x 'done'"
    := (stmt_while [c; x])
        : LangImpScope
    .

    Definition isValueE (x : Expression2) : Expression2 :=
         ((isZ x) || (isBool x) || (e_fun b_have_same_symbol [e_ground (t_term "unitValue" []); x]))%rs
    .

    Definition isNonValueE := fun x => (e_fun b_bool_neg [(isValueE x)]).

    Definition isValue := fun x => mkSideCondition2 _ b_cond_is_true [isValueE x].

    #[local]
    Instance ImpDefaults : Defaults := {|
        default_cseq_name := u_cseq_name ;
        default_empty_cseq_name := u_empty_cseq_name ;
        default_context_template
            := (context-template u_cfg ([ u_state [HOLE; (t_over ($X)) ] ]) with HOLE) ;

        default_isValue := isValue ;
        default_isNonValue := fun x => mkSideCondition2 _ b_cond_is_true [isNonValueE x] ;
    |}.


    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'where' c" := (
        decl_rule (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l; t_over ($REST_SEQ) ]; t_over ($VALUES) ] ]
         ~>{default_act} u_cfg [ u_state [ u_cseq [ r; t_over ($REST_SEQ) ]; t_over ($VALUES) ] ]
         where (c)
        )
    ) (at level 90).

    Notation "'decl_simple_rule' '[' s ']:' l '~>' r 'always'" := (
        decl_rule (
        rule [ s ]:
            u_cfg [ u_state [ u_cseq [ l; t_over ($REST_SEQ) ]; $VALUES ] ]
         ~>{default_act} u_cfg [ u_state [ u_cseq [ r; t_over ($REST_SEQ) ]; t_over ($VALUES) ] ]
        )
    ) (at level 90).

    Definition Decls : list Declaration := [
        (decl_strict (symbol "arith_plus" of arity 2 strict in [0;1]));
        (decl_strict (symbol "arith_minus" of arity 2 strict in [0;1]));
        (decl_strict (symbol "arith_times" of arity 2 strict in [0;1]));
        (decl_strict (symbol "arith_div" of arity 2 strict in [0;1]));
        (* plus *)
        (decl_simple_rule ["plus-Z-Z"]: (t_over ($X) + t_over ($Y)) ~> t_over ($X +Z $Y) where [mkSideCondition2 _ b_cond_is_true [((isZ ($X)) && (isZ ($Y)))]]);
        (* minus *)
        (decl_simple_rule ["minus-Z-Z"]:
               (t_over ($X) - t_over ($Y))
            ~> t_over ($X -Z $Y)
                where [mkSideCondition2 _ b_cond_is_true[(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )]])
        ;
        (* times *)
        (decl_simple_rule ["times-Z-Z"]:
               (t_over ($X) * t_over ($Y))
            ~> t_over ($X *Z $Y)
                where [mkSideCondition2 _ b_cond_is_true[(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                )]])
        ;
        (* div *)
        (decl_simple_rule ["div-Z-Z"]:
                (t_over($X) / t_over($Y))
            ~> t_over($X /Z $Y)
                where [mkSideCondition2 _ b_cond_is_true[(
                    (isZ ($X))
                    &&
                    (isZ ($Y))
                    (* TODO test that $Y is not 0*)
                )]])
        ;
        
        (decl_strict (symbol "stmt_assign" of arity 2 strict in [1]));

        (decl_rule (
            rule ["assign-value"]:
                u_cfg [ u_state [ u_cseq [ (var [t_over ($X)]) <:= t_over ($Y); t_over ($REST_SEQ)]; t_over ($VALUES) ] ]
            ~>{default_act} u_cfg [ u_state [
                    u_cseq [unitValue[]; t_over ($REST_SEQ)];
                    t_over (e_fun b_map_update [($VALUES); ($X); ($Y)])
                ] ]
                where [mkSideCondition2 _ b_cond_is_true [((isString ($X)) && (isValueE ($Y)))]]
        ));
        (decl_rule (
            rule ["var-lookup"]:
                u_cfg [ u_state [ u_cseq [ var [t_over ($X) ]; t_over ($REST_SEQ)]; t_over ($VALUES)]]
            ~>{default_act} u_cfg [ u_state [
                u_cseq [t_over (e_fun b_map_lookup [($VALUES); ($X)]); t_over ($REST_SEQ)];
                t_over ($VALUES)
            ]]
        ));
        (* TODO stmt_seq does not have to be strict in the second argument, and the following rule does not need to check the value-ness of the second argument*)
        (decl_simple_rule ["seq-unit-value"]:
                stmt_seq [unitValue []; t_over ($X) ]
            ~> t_over ($X)
            where [mkSideCondition2 _ b_cond_is_true[((isValueE ($X)))]])
        ;
        (decl_strict (symbol "stmt_seq" of arity 2 strict in [0;1]));

        (decl_strict (symbol "bexpr_eq" of arity 2 strict in [0;1]));
        (decl_strict (symbol "bexpr_negb" of arity 1 strict in [0]));
        (decl_strict (symbol "bexpr_le" of arity 2 strict in [0;1]));
        (decl_strict (symbol "bexpr_lt" of arity 2 strict in [0;1]));

        (decl_simple_rule ["bexpr-eq-Z-Z"]:
                bexpr_eq [ t_over ($X); t_over ($Y) ]
            ~> (t_over (e_fun b_bool_eq [($X); ($Y)]))
            where [mkSideCondition2 _ b_cond_is_true[((isValueE ($X)) && (isValueE ($Y)))]])
        ;
        (decl_simple_rule ["bexpr-le-Z-Z"]:
                bexpr_le [ t_over ($X); t_over ($Y) ]
            ~> (t_over (e_fun b_Z_isLe [($X); ($Y)]))
            where [mkSideCondition2 _ b_cond_is_true[((isZ ($X)) && (isZ ($Y)))]])
        ;
        (decl_simple_rule ["bexpr-lt-Z-Z"]:
               bexpr_lt [ t_over ($X); t_over ($Y) ]
            ~> (t_over (e_fun b_Z_isLt [($X); ($Y)]))
            where [mkSideCondition2 _ b_cond_is_true[((isZ ($X)) && (isZ ($Y)))]])
        ;
        (decl_simple_rule ["bexpr-negb-bool"]:
               bexpr_negb [t_over ($X) ]
            ~> t_over (e_fun b_bool_neg [($X)])
            where [mkSideCondition2 _ b_cond_is_true[((isBool ($X)))]])
        ;
        (decl_strict (symbol "stmt_ite" of arity 3 strict in [0]) );
        (decl_simple_rule ["stmt-ite-true"]: stmt_ite [t_over ($B); t_over ($X); t_over ($Y)] ~> t_over ($X) where [mkSideCondition2 _ b_cond_is_true[($B)]]) ;
        (decl_simple_rule ["stmt-ite-false"]: stmt_ite [t_over ($B); t_over ($X); t_over ($Y)] ~> t_over ($Y) where [mkSideCondition2 _ b_cond_is_true[($B ==Bool false)]]) ;
        (* (* sugared *)
        decl_simple_rule ["while-unfold"]:
            stmt_while [$B, $X]
            ~> (if ($B) then (($X); then stmt_while [$B, $X]) else (unitValue []))
            always
        *)
        (decl_simple_rule ["while-unfold"]:
            stmt_while [t_over ($B) ; t_over ($X)]
            ~> stmt_ite [t_over ($B) ; stmt_seq [t_over ($X); stmt_while [t_over ($B); t_over ($X)]]; unitValue [] ]
            where [])
    ]%limp.

    Definition Γ : (RewritingTheory2 Act)*(list string) := Eval vm_compute in 
    (to_theory Act (process_declarations Act default_act _ mypi (Decls))).

    (* Compute (length (Γ.1)). *)


    Definition initial0 (x : TermOver builtin_value) :=
        (ground (
            u_cfg [ u_state [ u_cseq [x; u_emptyCseq [] ] ; (builtin_function_interp b_map_empty (nondet_gen 0) []) ] ]
        ))
    .

    (* About RewritingTheory2_wf_heuristics. *)
    Lemma interp_sound:
        Interpreter_sound'
        (Γ.1)
        (naive_interpreter Γ.1) 
    .
    Proof.
        apply naive_interpreter_sound.
        ltac1:(assert(Htmp: isSome(RewritingTheory2_wf_heuristics (Γ.1)))).
        {
            ltac1:(compute_done).
        }
        unfold is_true, isSome in Htmp.
        destruct (RewritingTheory2_wf_heuristics Γ.1) eqn:Heq>[|inversion Htmp].
        assumption.
    Qed.

    Definition imp_interp_from (fuel : nat) (from : (TermOver builtin_value))
        := interp_loop nondet_gen 1 (naive_interpreter Γ.1 (t_over bv_error)) fuel (ground (initial0 from))
    .

    (*  
    Compute (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((term_operand (bv_Z 89))) ; then
        ((term_operand (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp)).

    *)

    Lemma test_imp_interp_1:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 12 (ground (
        (var [builtin_string "x"]) <:= ((t_over (bv_Z 89))) ; then
        ((t_over (bv_Z 3)) + (var [builtin_string "x"]))
        )%limp))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(t_over (bv_Z 92)); u_emptyCseq [] ] ; t_over m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.
    
    Definition program_2 := (ground (
        (var [builtin_string "x"]) <:= ((t_over (bv_Z 89))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (t_over (bv_Z 90))) )
         then (t_over (bv_Z 10)) else (t_over (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_2). *)
    Lemma test_imp_interp_5:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_2)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(t_over (bv_Z 10)); u_emptyCseq [] ] ; t_over m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.
    
    Definition program_3 := (ground (
        (var [builtin_string "x"]) <:= ((t_over (bv_Z 91))) ; then
        (if(
            ( (var [builtin_string "x"]) <= (t_over (bv_Z 90))) )
         then (t_over (bv_Z 10)) else (t_over (bv_Z 20))
        )
        )%limp).

    (* Compute (imp_interp_from 15 program_3). *)
    Lemma test_imp_interp_program_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 15 program_3)
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(t_over (bv_Z 20)); u_emptyCseq [] ] ; t_over m ] ]
            )%limp)
        )
    .
    Proof.
        eexists. eexists. reflexivity.
    Qed.

    Notation "'v' '(' s ')'" := (var [builtin_string s]).

    (* Definition n {_br : BasicResolver} := (ground(v("n"))). *)

    Definition program_count_to (n : Z) := (ground (
        (v("n")) <:= ((t_over (bv_Z n))) ; then
        (v("sum")) <:= ((t_over (bv_Z 0))) ; then
        (while(((t_over (bv_Z 1)) <= (v("n")))) do (
            (v("sum")) <:= ((v("sum")) + ((v("n")))); then
            (v("n")) <:= ((v("n")) + (t_over (bv_Z (-1))))
        ) done
        );then (v("sum"))
        )%limp).

    (* Time Compute ((imp_interp_from 1000 (program_count_to 3))). *)
    Lemma test_imp_interp_program_count_to_3:
        exists (rem : nat) (m : BuiltinValue),
        (imp_interp_from 1000 (program_count_to 3))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(t_over (bv_Z 6)); u_emptyCseq nil ] ; t_over m ] ]
            )%limp)
        )
    .
    Proof.
        ltac1:(vm_compute).
        eexists. eexists. reflexivity.
    Qed.

    (* The proof and QED time of this lemma are too high, so I do not want to run them every time I compile this file.*)
    (*
    Lemma test_imp_interp_program_count_to_10:
        exists (rem : nat) (log : string) (m : BuiltinValue),
        (imp_interp_from 1000 (program_count_to 10))
        = (
            rem,
            (ground (
                u_cfg [ u_state [ u_cseq [(term_operand (bv_Z 55)), u_emptyCseq [] ] , m ] ]
            )%limp),
            log
        )
    .
    Proof.
        eexists. eexists. eexists. reflexivity.
    Qed.
    *)

    
    Definition interp_program_count_to (fuel : nat) (n : Z)
    :=
        let r := imp_interp_from fuel (program_count_to n) in
        let n : Z := (match r.2 with
        | t_term "u_cfg" [t_term "u_state" [t_term "u_cseq" [t_over (bv_Z val)]; t_term "u_empty_cseq" nil]]
          => val
        | _ => Z0
        end) in
        (r.1,n)
    .

End imp.


From Minuska Require Import
    prelude
    spec
    ocaml_interface
.


Inductive Emptyset : Set := .

#[export]
Instance emptyset_eqdec : EqDecision Emptyset.
Proof.
    intros x y.
    destruct x, y.
Defined.

#[export]
Program Instance emptyset_fin : Finite Emptyset := {|
    enum := [];
|}.
Next Obligation.
    constructor.
Qed.
Next Obligation.
    destruct x.
Qed.
Fail Next Obligation.


Section sec.

    Context
        {symbol : Set}
        {symbols : Symbols symbol}
    .

    #[local]
    Program Instance mysignature : Signature := {|
        builtin_function_symbol
            := Emptyset ;
        builtin_predicate_symbol
            := Emptyset ;
    |}.
    Fail Next Obligation.

    Program Definition βover
        : ModelOver mysignature MyUnit Emptyset := {|
        builtin_function_interp
            := fun _ _ _ => None ;
        builtin_predicate_interp
            := fun _ _ _ => None ;
    |}.
    Fail Next Obligation.

    #[local]
    Instance β
        : @Model _ _ mysignature MyUnit := {|
        builtin_value
            := Emptyset ;
        builtin_model_over := βover ;
    |}.

End sec.

Definition bindings (Q : Type) : string -> SymbolInfo Emptyset void Emptyset void Q void
:=
    fun s => si_none _ _ _ _ _ _
.
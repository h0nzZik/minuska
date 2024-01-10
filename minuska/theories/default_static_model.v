From Minuska Require Import
    prelude
    spec_syntax
    spec_semantics
    string_variables
    empty_builtin
    flattened
.


#[export]
Instance MySymbols : Symbols string := Build_Symbols _ _ _.

#[export]
Program Instance Σ : StaticModel := {|
    symbol := string ;
    variable := string ;
    symbols :=  MySymbols;
    variables := StringVariables ;
|}.
Next Obligation.
    apply EmptyBuiltin.
Defined.


#[export]
Program Instance CΣ : @ComputableStaticModel Σ := {|
    builtin_unary_predicate_interp_bool := fun _ _ => false ;
    builtin_binary_predicate_interp_bool := fun _ _ _ => false ;
|}.
Next Obligation.
    destruct p.
Qed.
Next Obligation.
    destruct p.
Qed.
Fail Next Obligation.
From Minuska Require Import
    prelude
    spec
    string_variables
.

#[export]
Instance MySymbols : Symbols string := Build_Symbols _ _ _.

Section default_model.
    Context
        (β : Builtin)
    .

    Definition default_model : StaticModel := {|
        symbol := string ;
        variable := string ;
        symbols :=  MySymbols;
        variables := StringVariables ;
        builtin := β ;
    |}.


End default_model.
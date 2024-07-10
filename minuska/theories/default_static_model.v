From Minuska Require Import
    prelude
    spec
    string_variables
.

#[export]
Instance MySymbols : Symbols string := Build_Symbols _ _ _.

Section default_model.
    Context
        (β : Builtin unit)
    .

    CoFixpoint trivial_stream : Stream unit
    := Seq unit () trivial_stream.
    
    Definition default_model : StaticModel := {|
        symbol := string ;
        variable := string ;
        symbols :=  MySymbols;
        variables := StringVariables ;
        builtin := β ;
        (* nondet_stream := trivial_stream; *)
        nondet_gen := fun _ => () ;
    |}.


End default_model.
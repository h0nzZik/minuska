From Minuska Require Import
    prelude
    spec
    string_variables
.

#[export]
Instance MySymbols : Symbols string := Build_Symbols _ _ _.

Section default_model.
    Context
        (signature : Signature)
        (β : Model signature MyUnit)
        (my_program_info : ProgramInfo)
    .

    CoFixpoint trivial_stream : Stream MyUnit
    := Seq MyUnit mytt trivial_stream.
    
    Definition default_model : StaticModel := {|
        symbol := string ;
        variable := string ;
        symbols :=  MySymbols;
        variables := StringVariables ;
        builtin := β ;
        program_info := my_program_info ;
        (* nondet_stream := trivial_stream; *)
        nondet_gen := fun _ => mytt ;
    |}.


End default_model.
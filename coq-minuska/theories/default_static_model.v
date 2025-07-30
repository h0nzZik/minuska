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
        (hidden_signature : HiddenSignature)
        (β : Model signature MyUnit)
        (Hβ : HiddenModel signature hidden_signature β)
        (my_program_info : ProgramInfo)
    .

    CoFixpoint trivial_stream : Stream MyUnit
    := Seq MyUnit mytt trivial_stream.
    
    Definition default_model : BackgroundModel := {|
        TermSymbol := string ;
        Variabl := string ;
        TermSymbols :=  MySymbols;
        Variabls := StringVariables ;
        builtin := β ;
        hidden := Hβ ;
        program_info := my_program_info ;
        (* nondet_stream := trivial_stream; *)
        nondet_gen := fun _ => mytt ;
    |}.


End default_model.
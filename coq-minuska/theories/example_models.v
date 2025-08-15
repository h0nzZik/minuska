From Minuska Require Import
    prelude 
    spec
    builtin.int_signature
    builtin.int_model
    pi.trivial
    hidden.hidden_unit
.

Definition Σ1 : BackgroundModel := {|
    basic_types := {|
        Variabl := string ;
        TermSymbol := string ;
        FunSymbol := _ ;
    |};
    basic_types_properties := {|
        Variabl_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        TermSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        FunSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        PredSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        HPredSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        AttrSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        QuerySymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        MethSymbol_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        BasicValue_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        HiddenValue_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
        NondetValue_edc := {|
            edc_eqdec := _ ;
            edc_count := _ ;
        |};
    |} ;
    background_model_over := {|
        value_algebra := int_va string unit ;
        hidden_algebra := hidden_unit.unit_hidden_model unit ;
        program_info := @pi.trivial.MyProgramInfo _ _ unit  ;
        nondet_gen := fun _ => tt ;
    |};
|}.


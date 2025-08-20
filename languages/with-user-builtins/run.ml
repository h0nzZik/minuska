open Core
open Libminuska
open Miskeleton
open Libminuskapluginbase
open Pluginbase


let my_interface = (
  let m  = (Myalgebra.list_int_model) in
  let hm = (Extracted.top_hidden_unit_model) in
  let pi = (Extracted.top_pi_trivial_pi) in
  let bs = (Extracted.combine_symbol_classifiers
    (Myalgebra.bindings)
    (Extracted.top_pi_trivial_bindings)
    (Extracted.top_hidden_unit_bindings)
  ) in
  {
    v_edc = Myalgebra.list_int_v_edc;
    ts_edc = Extracted.top_string_symbols_edc;
    fs_edc = Myalgebra.fs_edc;
    ps_edc = Myalgebra.ps_edc;
    qs_edc = Extracted.top_pi_trivial_qs_edc;
    hv_edc = Extracted.top_hidden_unit_edc;
    ats_edc = Extracted.top_hidden_unit_ats_edc;
    ms_edc = Extracted.top_hidden_unit_ms_edc;
    hps_edc = Extracted.top_hidden_unit_hps_edc;
    nv_edc = Extracted.top_nv_edc;
    vr_edc = Extracted.top_string_symbols_edc;
    vr_inf = Extracted.top_string_infinite;
    background_model = {
        value_algebra = m;
        hidden_algebra = hm;
        program_info = pi;
        nondet_gen = (fun _ -> ());
    };
    builtin_inject = empty_builtin_inject;
    builtin_eject = empty_builtin_eject;
    bindings = bs;
  }
)



let main () =
  Libminuska.Miskeleton.main
    my_interface
    (fun _ -> raise (Failure "Parser not implemented"))
    Internal.langDefaults
    Internal.lang_Decls
  
let _ = main ()
    

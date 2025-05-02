open Core
open Printf
open Libminuskapluginbase
open Pluginbase

let main () =
  let pvae = (get_primitive_value_algebra (coqModuleName_of_sexp (Sexp.of_string ("(Std_module klike)")))) in
  let signature = (pvae.pvae_builtin_interface.bi_signature) in
  let builtins = (pvae.pvae_builtin_interface.bi_beta) in
  let pie = (get_trivial_program_info signature builtins) in

  Libminuska.Miskeleton.main
    pvae
    pie
    Imp.Transform.parse
    Imp.Internal.langDefaults
    Imp.Internal.lang_Decls
  
let _ = main ()
    

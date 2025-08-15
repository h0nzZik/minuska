open Core
open Printf
open Libminuskapluginbase
open Pluginbase

let main () =
  Libminuska.Miskeleton.main
    Libminuska.Miskeleton.klike_interface
    Transform.parse
    Internal.langDefaults
    Internal.lang_Decls
  
let _ = main ()
   

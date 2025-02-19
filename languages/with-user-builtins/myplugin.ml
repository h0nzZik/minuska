open Core

let () =
  printf "Hello, plugin: %n\n" (Z.to_int (Myalgebra.fancy_number));
  ()

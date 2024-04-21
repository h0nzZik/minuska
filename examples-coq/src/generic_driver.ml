open Format

let usage_msg = "generic_driver [-depth <number3> ]"

let depth = ref 10000

let anon_fun mynum = ()

let speclist =
  [
    ("-depth", Arg.Set_int depth, "Maximal execution depth")
  ]

let () =
  Arg.parse speclist anon_fun usage_msg;
  printf "Running for %d steps.\n" !depth;
  let res = result !depth in
  printf "Remaining fuel: %d\n" (snd res)


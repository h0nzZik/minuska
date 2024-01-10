open Format
open TwoCounters

let usage_msg = "two_counters_driver -m <number1> -n <number2> [-depth <number3> ]"

let depth = ref 10

let number1 = ref 10
let number2 = ref 0


let anon_fun mynum = ()

let speclist =
  [
    ("-depth", Arg.Set_int depth, "Maximal execution depth");
    ("-m", Arg.Set_int number1, "number1");
    ("-n", Arg.Set_int number2, "number2")
  ]

let () =
  Arg.parse speclist anon_fun usage_msg;
  (* Main functionality here *)
  print_string "Hello world!\n";
  print_string (string_of_int !number1);
  print_string (string_of_int !number2);
  print_string (string_of_int !depth);
  let result = TwoCounters.Coq_two_counters.interp_loop_number !depth !number1 !number2 in
  match result with
  | None -> print_string "None"
  | Some x ->
    printf "Some (%d,%d)" (fst x) (snd x)
  
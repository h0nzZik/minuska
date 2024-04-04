open ExampleLang

let usage_msg = "example_langdriver <number>"

let depth = ref 10

let number = ref 0


let anon_fun mynum =
  number := int_of_string mynum

let speclist =
  [
    ("-depth", Arg.Set_int depth, "Maximal execution depth")
  ]

let () =
  Arg.parse speclist anon_fun usage_msg;
  (* Main functionality here *)
  print_string "Hello world!\n";
  print_string (string_of_int !number);
  print_string (string_of_int !depth);
  let result = ExampleLang.Coq_example_1.interp_loop_number !depth !number in
  match result with
  | None -> print_string "None"
  | Some x -> print_string "Some"; print_string (string_of_int x)
  
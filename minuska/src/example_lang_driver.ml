open ExampleLang

let usage_msg = "example_langdriver [-verbose] <number>"

let verbose = ref false

let number = ref 0


let anon_fun mynum =
  number := int_of_string mynum

let speclist =
  [("-verbose", Arg.Set verbose, "Output debug information")
  ]

let () =
  Arg.parse speclist anon_fun usage_msg;
  (* Main functionality here *)
  print_string "Hello world!\n";
  print_string (string_of_int !number);
  let result = interp_number !number in
  result
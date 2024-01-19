open Format
open SumToN
open Printexc

module B = Big_int_Z

let usage_msg = "fib_native_driver [-depth <number> ] -n <N>"

let depth = ref 10000
let n = ref 0
let do_log = ref 0

let anon_fun mynum = ()

let speclist =
  [
    ("-depth", Arg.Set_int depth, "Maximal execution depth");
    ("-log", Arg.Set_int do_log, "Print log?");
    ("-n", Arg.Set_int n, "N-th number to compute")
  ]

let main () =
  Arg.parse speclist anon_fun usage_msg;
  printf "Running for %d steps.\n" !depth;
  let res = SumToN.Coq_imp.interp_program_count_to !depth (B.big_int_of_int !n) in
  let sum_n = snd (fst res) in
  printf "sum_to_n(%d) = %d\n" !n (B.int_of_big_int sum_n);
  printf "Remaining fuel: %d\n" (fst (fst res));
  let log = String.of_seq (List.to_seq (snd res)) in
  if !do_log > 0 then (printf "Log: %s.\n" log; ()) else ();
  ()

let () =
    Printexc.record_backtrace true;
    try main() with Stack_overflow -> (printf "Stack overflow.\n%s" (Printexc.get_backtrace ()));;


open Core
open Printf

let format_string_list0 (open_br : string) (close_br: string) (sep : string) (l : string list) : string =
  match l with
  | [] -> (sprintf "%s%s" open_br close_br)
  | x::[] -> (sprintf "%s %s %s" open_br x close_br)
  | x::y::zs ->
    (sprintf "%s %s%s %s" open_br x (List.fold_left ~init:("") ~f:(fun b a -> sprintf "%s%s%s" b sep a) (y::zs)) close_br )

let format_string_list (l : string list) : string =
  (format_string_list0 "[" "]" ", " l)

let format_coq_string_list (l : string list) : string =
  (format_string_list0 "[" "]" "; " l)

let format_coq_string_list_per_line (l : string list) : string =
  (format_string_list0 "[" "]" ";\n" l)

let format_string_list_per_line (l : string list) : string =
  (format_string_list0 "" "" "\n" l)

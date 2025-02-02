open Core


let mymap (f : 'a -> 'b) (g : 'b -> 'b) (l : 'a list)  : 'b list =
    let ln = List.length l in
    List.mapi ~f:(fun idx x -> if (idx + 1 = ln) then (f x) else (g (f x))) l


let builtin_to_string (b : Syntax.builtin) : string =
  match b with
  | `BuiltinInt n -> "(@builtin-int " ^ (string_of_int n) ^ ")"
  | `BuiltinString s -> "(@builtin-string \"" ^ s ^ "\")"
  | `BuiltinBool b -> "(@builtin-bool " ^ (if b then "true" else "false") ^ "\")"
  | `BuiltinError -> "(@builtin-error)"
  | `OpaqueBuiltin -> "(@opaque_builtin)"

let rec groundterm_to_string (g : Syntax.groundterm) : string =
  match g with
  | `GTb b -> "[" ^ (builtin_to_string b) ^ "]"
  | `GTerm (`Id s, gs) ->
    s ^ "[" ^ (String.concat (mymap groundterm_to_string (fun x -> x ^ ", ") gs)) ^ "]"


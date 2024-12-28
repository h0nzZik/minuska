%token <int> INT

%token EOF

%start <(int option)> option_int
%{ open Syntax %}
%%

option_int:
  | EOF { None }
  | x = INT
    EOF
    { Some x }
  ;
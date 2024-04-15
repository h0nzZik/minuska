%token <int> INT
%token <string> ID
%token <string> VAR
%token KEYWORD_SYMBOLS
%token KEYWORD_VALUE
%token KEYWORD_STRICTNESS
%token KEYWORD_RULE
%token KEYWORD_OF
%token KEYWORD_ARITY
%token KEYWORD_IN
%token KEYWORD_WHERE
%token BRACKET_ROUND_LEFT
%token BRACKET_ROUND_RIGHT
%token BRACKET_SQUARE_LEFT
%token BRACKET_SQUARE_RIGHT
%token SLASH
%token ARROW
%token SEMICOLON
%token COLON
%token COMMA
%token EOF



%start <(Syntax.definition option)> definition
%{ open Syntax %}
%%

symbolsdecl:
  | KEYWORD_SYMBOLS
    COLON
    BRACKET_SQUARE_LEFT
    v = separated_list(COMMA, ID)
    BRACKET_SQUARE_RIGHT
    SEMICOLON
    { v }
  ;

strictnessone:
  | s = ID;
    KEYWORD_OF;
    KEYWORD_ARITY;
    n = INT;
    KEYWORD_IN;
    BRACKET_SQUARE_LEFT;
    pos = separated_list(COMMA, INT);
    BRACKET_SQUARE_RIGHT;
    SEMICOLON;
    { { symbol = (`Id s); arity = n; strict_places = pos } }
  ;

strictnessall:
  | KEYWORD_STRICTNESS;
    COLON;
    BRACKET_SQUARE_LEFT;
    ss = separated_list(COMMA, strictnessone);
    BRACKET_SQUARE_RIGHT;
    SEMICOLON;
    { ss }
  ;


pattern:
  | x= VAR
    { `PVar (`Var x) }
  | s = ID
    BRACKET_SQUARE_LEFT 
    es = separated_list(COMMA, pattern)
    BRACKET_SQUARE_RIGHT
    { `PTerm ((`Id s), es) }
  ;

groundterm:
  | s = ID;
    BRACKET_SQUARE_LEFT
    ts = separated_list(COMMA, groundterm)
    BRACKET_SQUARE_RIGHT
    { `GTerm ((`Id s),ts)}
  ;  


expr:
  | x = VAR
    { `EVar (`Var x) }
  | 
    BRACKET_SQUARE_LEFT
    g = groundterm
    BRACKET_SQUARE_RIGHT
    { `EGround g }
  | s = ID
    BRACKET_ROUND_LEFT
    es = separated_list(COMMA, expr)
    BRACKET_ROUND_RIGHT
    { `ECall ((`Id s),es) }
  ;

exprterm:
  | e = expr
    { `EExpr e }
  | s = ID
    BRACKET_SQUARE_LEFT
    ts = separated_list(COMMA, exprterm)
    BRACKET_SQUARE_RIGHT
    { `ETerm ((`Id s), ts) }
  ;

valuedecl:
  | KEYWORD_VALUE
    BRACKET_ROUND_LEFT
    x = VAR 
    BRACKET_ROUND_RIGHT
    COLON 
    BRACKET_ROUND_LEFT
    e = expr
    BRACKET_ROUND_RIGHT
    SEMICOLON
    { (x,e) }
  ;

rule:
  | KEYWORD_RULE
    BRACKET_SQUARE_LEFT
    n = ID
    BRACKET_SQUARE_RIGHT
    COLON
    l = pattern
    ARROW
    r = exprterm
    KEYWORD_WHERE
    c = expr
    SEMICOLON
    { {name = n; lhs = l; rhs = r; cond = c }  }
  ;

definition:
  | EOF            { None }
  | syms = symbolsdecl
    v = valuedecl
    sall = strictnessall
    rs = list(rule)
    EOF
    { Some { symbols = (List.map (fun x -> `Id x) syms); value = (`Var (fst v), (snd v)); strictness = sall; rules = rs } }
  ;

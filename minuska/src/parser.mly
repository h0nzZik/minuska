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



%start <minuska.definition option> definition
%{ open Syntax %}


%type <(id list)> symbolsdecl
%type <expr> expr
%type <pattern> pattern
%type <exprterm> exprterm
%type <groundterm> groundterm
%type <rule> rule
%type <strictdecl> strictnessone
%type <(strictdecl list)> strictnessall
%type <rule list> list(rule)
%%

symbolsdecl:
  | KEYWORD_SYMBOLS
    COLON
    v = separated_list(COMMA, ID)
    SEMICOLON
    { v }
  ;

strictnessone:
  | s = ID
    KEYWORD_OF
    KEYWORD_ARITY
    n = INT
    KEYWORD_IN
    BRACKET_SQUARE_LEFT
    pos = separated_list(COMMA, INT)
    BRACKET_SQUARE_RIGHT
    SEMICOLON
    {  }
  ;

strictnessall:
  | KEYWORD_STRICTNESS
    COLON
    ss = separated_list(COMMA, strictnessone)
    { ss }
  ;


pattern:
  | x = VAR
    { `PVar x }
  | s = ID
    BRACKET_SQUARE_LEFT
    es = separated_list(COMMA, pattern)
    BRACKET_SQUARE_RIGHT
    { PTerm s es }
  ;

groundterm:
  | s = ID
    ts = separated_list(COMMA, groundterm)
    { (GTerm s ts) }
  ;  


expr:
  | x = VAR
    { `EVar x }
  | g = groundterm
    { `EGround g }
  | s = ID
    BRACKET_ROUND_LEFT
    es = separated_list(COMMA, expr)
    BRACKET_ROUND_RIGHT
    { `ETCall s es }
  ;

exprterm:
  | e = expr
    { `EExpr e }
  | s = ID
    BRACKET_SQUARE_LEFT
    ts = separated_list(COMMA, exprterm)
    BRACKET_SQUARE_RIGHT
    { `ETerm s ts }
  ;

valuedecl:
  | KEYWORD_VALUE
    BRACKET_ROUND_LEFT
    x = VAR 
    BRACKET_ROUND_RIGHT
    COLON 
    e = expr
    SEMICOLON
    { (x,expr) }
  ;

rule:
  | KEYWORD_RULE
    BRACKET_SQUARE_LEFT
    name = ID
    BRACKET_SQUARE_RIGHT
    COLON
    l = pattern
    ARROW
    r = exprterm
    KEYWORD_WHERE
    c = expr
    SEMICOLON
    { {lhs = l rhs = r cond = c }  }
  ;

definition:
  | EOF            { None }
  | syms = symbolsdecl
    v = valuedecl
    sall = strictnessall
    rs = list(rule)
    EOF
    { { symbols = syms value = v strictness = sall rules = rs } }
  ;

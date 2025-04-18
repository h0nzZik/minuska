%token <int> INT
%token <string> ID
%token <string> VAR
%token <string> STRING
%token KEYWORD_VALUE
%token KEYWORD_STRICTNESS
%token KEYWORD_BUILTIN
%token KEYWORD_RULE
%token KEYWORD_FRAMES
%token KEYWORD_OF_ARITY
%token KEYWORD_IN
%token KEYWORD_WHERE
%token KEYWORD_CONTEXT
%token KEYWORD_TRUE
%token KEYWORD_FALSE
%token KEYWORD_AND
%token KEYWORD_OR
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



%{ open Libminuskapluginbase %}
%start <(Syntax.definition option)> option_definition
%start <(Syntax.groundterm option)> option_groundterm
%{ open Syntax %}
%%

contextdecl:
  | KEYWORD_CONTEXT
    BRACKET_ROUND_LEFT
    x = VAR
    BRACKET_ROUND_RIGHT
    COLON
    p = pattern
    SEMICOLON
    { { cd_var = (`Var x); cd_pat = p } }

strictnessone:
  | s = ID;
    KEYWORD_OF_ARITY;
    n = INT;
    KEYWORD_IN;
    BRACKET_SQUARE_LEFT;
    pos = separated_list(COMMA, INT);
    BRACKET_SQUARE_RIGHT;
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

builtin:
  | BRACKET_ROUND_LEFT
    KEYWORD_BUILTIN
    COLON
    kind = ID
    BRACKET_ROUND_LEFT
    value = STRING
    BRACKET_ROUND_RIGHT
    BRACKET_ROUND_RIGHT
    { { br_kind = kind; br_value = value; } }
  ;

groundterm:
  | b = builtin
    { `GTb b }
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

condition:
  | KEYWORD_TRUE
    { `CondTrue }
  | KEYWORD_FALSE
    { `CondFalse }
  | p = ID
    BRACKET_ROUND_LEFT
    es = separated_list(COMMA, expr)
    BRACKET_ROUND_RIGHT
    { `CondAtomic ((`Id p), es) }
  | KEYWORD_OR
    BRACKET_ROUND_LEFT
    c1 = condition
    COMMA
    c2 = condition
    BRACKET_ROUND_RIGHT
    { `CondOr (c1, c2) }
  | KEYWORD_AND
    BRACKET_ROUND_LEFT
    c1 = condition
    COMMA
    c2 = condition
    BRACKET_ROUND_RIGHT
    { `CondAnd (c1, c2) }
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
    // BRACKET_ROUND_LEFT
    c = condition
    // BRACKET_ROUND_RIGHT
    SEMICOLON
    { (x,c) }
  ;

framedecl:
  | n = ID
    BRACKET_ROUND_LEFT
    x = VAR
    BRACKET_ROUND_RIGHT
    COLON
    p = pattern
    { { fd_name=(`Id n); fd_var=(`Var x); fd_pat=p } }
  ;

framesdecl:
  | KEYWORD_FRAMES
    COLON
    BRACKET_SQUARE_LEFT
    fs = separated_list(SEMICOLON, framedecl);
    BRACKET_SQUARE_RIGHT
    SEMICOLON
    { fs }
  ;

slashid:
  | SLASH
    x = ID
    { `Id x }
  ;

rule:
  | KEYWORD_RULE
    a = option(slashid)
    BRACKET_SQUARE_LEFT
    n = ID
    BRACKET_SQUARE_RIGHT
    COLON
    l = pattern
    ARROW
    r = exprterm
    KEYWORD_WHERE
    // BRACKET_SQUARE_LEFT
    c = condition
    // cs = separated_list(COMMA, condition);
    // BRACKET_SQUARE_RIGHT
    SEMICOLON
    { {frame = a; name = n; lhs = l; rhs = r; cond = c }  }
  ;

definition:
  | fs = framesdecl
    v = valuedecl
    c = contextdecl
    sall = strictnessall
    rs = list(rule)
    { { context = c; value = (`Var (fst v), (snd v)); frames = fs; strictness = sall; rules = rs } }
  ;

option_definition:
  | EOF { None }
  | d = definition
    EOF
    { Some d }

option_groundterm:
  | EOF { None }
  | g = groundterm
    EOF
    { Some g }

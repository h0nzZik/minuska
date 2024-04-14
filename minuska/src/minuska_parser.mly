%token <int> INT
%token <string> ID
%token KEYWORD_SYMBOLS
%token KEYWORD_VALUE
%token KEYWORD_STRICTNESS
%token KEYWORD_RULE
%token KEYWORD_OF
%token KEYWORD_ARITY
%token KEYWORD_IN
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



%start <imp.ast option> main

%type <aexpr> aexpr 
%type <bexpr> bexpr 
%type <stmt> stmt
%%


aexpr:
  | n = INT               { Some (IntConstant n) }
  | x = ID                { Some (IntVariable x) }
  | e1 = aexpr;
    PLUS;
    e2 = aexpr            { Some (IntPlus e1 e2) }
  ;

bexpr:
  | TRUE                  { Some (BoolConstant true) }
  | FALSE                 { Some (BoolConstant false) }
  | e1 = bexpr;
    AND;
    e2 = bexpr            { Some (BoolAnd e1 e2) }
  | NOT;
    e = bexpr             { Some (BoolNot e) }
  | e1 = aexpr;
    LEQ;
    e2 = aexpr            { Some (Leq e1 e2) }
  ;

stmt:
  | EOF                   { None }
  | e = aexpr             { Some e }
  | x = ID;
    COLONEQ;
    e = aexpr             { Some (AssignStmt x e) }
  | WHILE;
    LEFT_ROUND_BRACK;
    b = bexpr;
    RIGHT_ROUND_BRACK;
    LEFT_CURLY_BRACK;
    s = stmt;
    RIGHT_CURLY_BRACK;
    SEMICOLON             { Some (WhileStmt b s) }
  | s1 = stmt; s2 = stmt  { Some (SeqStmt s1 s2) }
  ;

main:
  | s = stmt; EOF { s }
  ;

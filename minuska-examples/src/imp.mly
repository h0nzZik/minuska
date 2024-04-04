%token <int> INT
%token <string> ID
%token TRUE
%token FALSE
%token AND
%token NOT
%token LEFT_CURLY_BRACK
%token RIGHT_CURLY_BRACK
%token LEFT_ROUND_BRACK
%token RIGHT_ROUND_BRACK
%token COMMA
%token WHILE
%token PLUS
%token SEMICOLON
%token COLONEQ
%token IF
%token LEQ
%token EOF


%start <imp.ast option> stmt
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
  | e1 = aepxr;
    LEQ;
    e2 = aepxr            { Some (Leq e1 e2) }
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
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



%start <imp.ast option> definition

%type <aexpr> aexpr 
%type <bexpr> bexpr 
%type <stmt> stmt
%%

decl:
  | KEYWORD_SYMBOLS;
    COLON;
    v = separated_list(COMMA, ID);
    SEMICOLON
    { SymbolsDecl v }

  | 

definition:
  | EOF            { None }
  | v = list(decl) { Some v }
  ;
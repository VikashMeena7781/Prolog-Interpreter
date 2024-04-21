%{
 open Ast
%}

%token <string> CONS VAR ArithOp ComOp EXCLAIM
%token LPAREN RPAREN COMMA DOT SEMICOL IMPLIES IS QUERY LBRACE RBRACE NOT Vertical_Line FAIL
%token EOF 

%start program
%type <program> program
%type <clause> clause
%type <atomic_formula> atomic_formula
%type <term> term
%type <term list> term_list


%left ArithOp
%left ComOp
%right NOT
%nonassoc IS
%nonassoc Vertical_Line


%%

program:
  | EOF                        {([], [])}
  | QUERY atomic_formula_list DOT            {([], $2)}
  | clause program             {let (clause_list, goals) = $2 in ($1::clause_list, goals)}
  

clause:
  | atomic_formula DOT                       { Fact($1) }
  | atomic_formula IMPLIES atomic_formula_list  DOT   {Rule($1, $3) }

term_list:
  term                  {[$1] }
  | term COMMA term_list {$1::$3 }
  | term SEMICOL term_list {$1::$3} 


atomic_formula_list:
  atomic_formula         {[$1] }
  | atomic_formula COMMA atomic_formula_list   { $1 :: $3 }
  | atomic_formula SEMICOL atomic_formula_list   { $1 :: $3 }

atomic_formula:
  EXCLAIM      {Exclaim($1)}
  | CONS LPAREN term_list RPAREN { FunctionForm($1, $3) }
  | term IS term   {FunctionForm_Is($1,$3)}
  // | NOT atomic_formula        {NotEqOp_1("+/", $2) }
  // | NOT LPAREN atomic_formula_list RPAREN    { NotEqOp("+/", $3) }
  | FAIL             {Reserved_Keyword_Fail("fail")}
  


term:
  VAR                    { Variable($1) }
  |  CONS          { Constant($1) }
  | CONS LPAREN term_list RPAREN {FunctionTerm($1, $3) }
  | term ArithOp term      { Arithmetic($1, $2, $3) }
  | LBRACE RBRACE            {Prolist([])}
  | LBRACE term_list RBRACE { Prolist($2) }
  | LBRACE term_list Vertical_Line term_list RBRACE   {Prolist_2($2,$4)}
  | term ComOp term        { Comparasion($1, $2, $3) }
  | NOT term        {NotEqOp("+/", $2) }
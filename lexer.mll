{
  open Parser
}

let int = '-'? ['0'-'9'] ['0'-'9']*

let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let temp1 = ['a'-'z']['a'-'z' 'A'-'Z' '0'-'9' '_']*
let var = ['A'-'Z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']*

let const = int | temp1


rule token = 
    parse
  | white    { token lexbuf }
  | newline  { Lexing.new_line lexbuf; token lexbuf }
  | "+/"               {NOT}
  | "is"                   { IS }
  | '('                    {  LPAREN }
  | "|"                    {Vertical_Line}
  | ')'                    {  RPAREN }
  | ','                    {  COMMA }
  | ';'                    {  SEMICOL }
  | "fail"                 {FAIL}
  | '.'                    {  DOT }
  | '!'                    {  EXCLAIM("!") }
  | "?-"                  {QUERY}
  | "["                   {LBRACE}
  |  "]"                   {RBRACE}
  | "+"             { ArithOp("plus") }
  | "-"            { ArithOp("minus") }
  | "*"            { ArithOp("mult") }
  | "/"          { ArithOp("div") }
  | "mod"           { ArithOp("mod") }
  | "**"           { ArithOp("power") }
  | "=:="                 { ComOp("equal_to") }
  | ">="                  { ComOp("greaterthan_equal_to") }
  | "=<"                  { ComOp("lessthan_equal_to") }
  | "<"                   { ComOp("lessthan") }
  | ">"                   { ComOp("greaterthan") }
  | "=/="                { ComOp("not_equalto") }
  | var as variable     {  VAR(variable) }
  | const as constant      {  CONS (constant) }
  | ":-"               {  IMPLIES }
  | eof                    {  EOF }
  | _                      { failwith ("Unexpected character: " ^ Lexing.lexeme lexbuf) }

and read_string buf =
  parse
  | '"'       {  (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Failure ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (Failure ("String is not terminated")) }

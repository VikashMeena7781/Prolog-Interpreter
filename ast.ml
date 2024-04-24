type term =
  | Variable of string
  | Constant of string
  | FunctionTerm of string * term list
  | Arithmetic of term * string * term
  | Prolist of term list
  | Any
  | Prolist_2 of term list * term list
  | Comparasion of term * string * term
  (* | NotEqOp of string * term *)

type atomic_formula =
  | FunctionForm of string * term list
  | FunctionForm_Is of term * term
  | NotEqOp of string * term list 
  (* | NotEqOp_1 of string * atomic_formula *)
  | Reserved_Keyword_Fail of string
  | Exclaim of string

type clause =
  | Fact of atomic_formula
  | Rule of atomic_formula * atomic_formula list


type goal = atomic_formula list

type program = clause list * goal

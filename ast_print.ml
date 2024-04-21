open Ast

let rec string_of_term = function
  | Variable v -> v
  | Constant c -> c
  | FunctionTerm (f, args) ->
      "Atomic_Formula(" ^ f ^ ", [" ^ String.concat "; " (List.map string_of_term args) ^ "])"
  | Arithmetic (t1, op, t2) ->
        "Arithmetic(" ^ op ^ "(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ "))"
  
  | Prolist terms ->
    "Prolist((" ^ String.concat "; " (List.map string_of_term terms) ^ "))"
  | Prolist_2 (head, tail) ->
      "Prolist(" ^ "Head of List :- [" ^ String.concat "; " (List.map string_of_term head) ^ "]" ^ ", Tail of List :- [" ^ String.concat "; " (List.map string_of_term tail) ^ "])"
  | Comparasion (t1, op, t2) ->
    "Comparasion(" ^ op ^ "(" ^ string_of_term t1 ^ ", " ^ string_of_term t2 ^ "))" 
  | NotEqOp(t1,t2) ->
    "Atomic_Formula_NOT(" ^ t1 ^ ", " ^ string_of_term t2 ^ ")"     


let rec string_of_atomic_formula = function
  | FunctionForm (p, terms) ->
      "Atomic_Formula(" ^ p ^ ", [" ^ String.concat "; " (List.map string_of_term terms) ^ "])"
  | FunctionForm_Is (t1, t2) ->
    "Atomic_Formula(" ^  string_of_term t1 ^ "; IS; " ^ string_of_term t2 ^ ")"
  (* | NotEqOp(t1,t2) ->
    "Atomic_Formula_NOT(" ^ t1 ^ ", [" ^ String.concat "; " (List.map string_of_atomic_formula t2) ^ "])" *)
  (* | NotEqOp_1(t1,t2) ->
    "Atomic_Formula_NOT(" ^ t1 ^ ", " ^ string_of_atomic_formula t2 ^ ")" *)
  | Reserved_Keyword_Fail(t1) ->
    "FAILS(" ^ t1 ^ ")"
  
  | Exclaim(t1) ->
    "Ofcourse(!)"


let rec string_of_clause = function
  | Fact atomic_formula ->
      "Fact(" ^ string_of_atomic_formula atomic_formula ^ ")"
  | Rule (head, body) ->
      "Rule([Head of program :-> " ^ string_of_atomic_formula head ^
      "; Body of program :-> [" ^ String.concat "; " (List.map string_of_atomic_formula body) ^ "]])"


let rec string_of_program prog =
  String.concat "\n" (List.map string_of_clause prog)

and string_of_goal goal =
  String.concat ", " (List.map string_of_atomic_formula goal)
  

let print_tree ast =
  let (clauses, goals) = ast in
  print_endline "Program:";
  print_endline (string_of_program clauses);
  print_endline "Goals:";
  print_endline (string_of_goal goals)

open Ast
open Lexing
open Ast
open Parser
open Ast_print

type substitution = (string, term) Hashtbl.t

(* Apply substitutions to a single term *)
let rec apply_sub_term term subs =
  match term with
  | Variable v -> (try Hashtbl.find subs v with Not_found -> term)
  | Constant c -> Constant c
  | FunctionTerm (f, args) -> FunctionTerm (f, List.map (fun arg -> apply_sub_term arg subs) args)
  | Arithmetic (t1, op, t2) -> Arithmetic (apply_sub_term t1 subs, op, apply_sub_term t2 subs)
  | Prolist terms -> Prolist (List.map (fun t -> apply_sub_term t subs) terms)
  | Prolist_2 (list1, list2) -> Prolist_2 (List.map (fun t -> apply_sub_term t subs) list1, List.map (fun t -> apply_sub_term t subs) list2)



(* Apply substitutions to an atomic_formula *)
let rec apply_sub_atomic_formula af subs =
  match af with
  | FunctionForm (name, terms) ->
    FunctionForm (name, List.map (fun term -> apply_sub_term term subs) terms)
  | FunctionForm_Is (t1, t2) ->
    FunctionForm_Is (apply_sub_term t1 subs, apply_sub_term t2 subs)
  | NotEqOp (name, afs) ->
    NotEqOp (name, List.map (fun af -> apply_sub_atomic_formula af subs) afs)
  | NotEqOp_1 (name, af) ->
    NotEqOp_1 (name, apply_sub_atomic_formula af subs)
  | Reserved_Keyword_Fail keyword ->
    Reserved_Keyword_Fail keyword
  | Comparasion (t1, op, t2) ->
    Comparasion (apply_sub_term t1 subs, op, apply_sub_term t2 subs)
  | Exclaim message ->
    Exclaim message


(* Apply substitutions to a list of atomic formulas (goals) *)
let apply_subs goals subs =
  List.map (fun goal -> apply_sub_atomic_formula goal subs) goals


(* unify terms  *)
let rec unify term1 term2 subs =
  match (term1, term2) with
  | Variable v, t | t, Variable v ->
      if Hashtbl.mem subs v then
          unify (Hashtbl.find subs v) t subs
      else
          (Hashtbl.add subs v t; Some subs)
  | Constant c1, Constant c2 when c1 = c2 ->
      Some subs
  | FunctionTerm (f1, args1), FunctionTerm (f2, args2) when f1 = f2 ->
      unify_lists args1 args2 subs
  | Arithmetic (t1, op1, t2), Arithmetic (t3, op2, t4) when op1 = op2 ->
      let subs1 = unify t1 t3 subs in
      (match subs1 with
       | None -> None
       | Some new_subs -> unify t2 t4 new_subs)
  | Prolist terms1, Prolist terms2 ->
      unify_lists terms1 terms2 subs
  | Prolist_2 (t1, t2), Prolist_2 (t3, t4) ->
    let subs1 = unify_lists t1 t3 subs in
    (match subs1 with
      | None -> None
      | Some new_subs -> unify_lists t2 t4 new_subs)
  | _ -> None

and unify_lists args1 args2 subs =
  match args1, args2 with
  | [], [] -> Some subs
  | t1 :: ts1, t2 :: ts2 ->
      let subs1 = unify t1 t2 subs in
      (match subs1 with
       | None -> None
       | Some new_subs -> unify_lists ts1 ts2 new_subs)
  | _ -> None


let rec unify_atomic af1 af2 subs =
  match (af1, af2) with
  | FunctionForm (name1, terms1), FunctionForm (name2, terms2) when name1 = name2 ->
    unify_lists terms1 terms2 subs
  | NotEqOp (name1, afs1), NotEqOp (name2, afs2) when name1 = name2 ->
    unify_atomic_formulas_list afs1 afs2 subs
  | FunctionForm_Is (t1, t2), FunctionForm_Is (t3, t4) ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end
  | NotEqOp_1 (name1, af1), NotEqOp_1 (name2, af2) when name1 = name2 ->
      unify_atomic af1 af2 subs
  | Comparasion (t1, op1, t2), Comparasion (t3, op2, t4) when op1 = op2 ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end
  (* | Reserved_Keyword_Fail kw1, Reserved_Keyword_Fail kw2 when kw1 = kw2 -> Some subs *)
  (* | Exclaim msg1, Exclaim msg2 when msg1 = msg2 -> Some subs *)
  | _ -> None  (* This case handles mismatches in atomic formula types or names *)


and unify_atomic_formulas_list afs1 afs2 subs =
  match (afs1, afs2) with
  | [], [] -> Some subs
  | af1 :: afs1', af2 :: afs2' ->
      begin match unify_atomic af1 af2 subs with
      | Some new_subs -> unify_atomic_formulas_list afs1' afs2' new_subs
      | None -> None
      end
  | _ -> None  

and unify_lists terms1 terms2 subs =
  match (terms1, terms2) with
  | [], [] -> Some subs
  | t1 :: ts1, t2 :: ts2 ->
      begin match unify t1 t2 subs with
      | Some new_subs -> unify_lists ts1 ts2 new_subs
      | None -> None
      end
  | _ -> None
  
    

let rec solve goals program =
  match goals with
  | [] -> true
  | g::gs ->
      program |> List.exists (fun rule ->
          match rule with
          | Fact f -> (match unify_atomic g f (Hashtbl.create 10) with
                      | Some subs -> solve (apply_subs gs subs) program
                      | None -> false)
          | Rule (head, body) -> (match unify_atomic g head (Hashtbl.create 10) with
                                  | Some subs -> solve (apply_subs (body @ gs) subs) program
                                  | None -> false)
      )

let main () =
  let rec read_eval_print env =
    print_string "?- ";
    flush stdout;
    let input = read_line () in
    if input = "halt." then
      ()
    else
      let lexbuf = Lexing.from_string input in
      try
        let result = Parser.program Lexer.token lexbuf in
        let (clauses, goals) = result in
        print_tree result;
        print_newline ();
        flush stdout;
        let updated_env = clauses @ env in
        if goals = [] then begin
          print_endline "OK";
          read_eval_print updated_env
        end else begin
          if solve goals updated_env then
            print_endline "Yes"
          else
            print_endline "No";
          read_eval_print updated_env
        end
      with
      | Parsing.Parse_error -> print_endline "Syntax error"; read_eval_print env
      | Failure err -> print_endline ("Error: " ^ err); read_eval_print env
  in
  read_eval_print []
  
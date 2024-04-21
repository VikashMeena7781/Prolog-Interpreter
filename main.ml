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
  | Comparasion (t1, op, t2) ->
    Comparasion (apply_sub_term t1 subs, op, apply_sub_term t2 subs)
  | NotEqOp (name, af) ->
    NotEqOp (name, apply_sub_term af subs)  



(* Apply substitutions to an atomic_formula *)
let rec apply_sub_atomic_formula af subs =
  match af with
  | FunctionForm (name, terms) ->
    FunctionForm (name, List.map (fun term -> apply_sub_term term subs) terms)
  | FunctionForm_Is (t1, t2) ->
    FunctionForm_Is (apply_sub_term t1 subs, apply_sub_term t2 subs)
  (* | NotEqOp (name, afs) ->
    NotEqOp (name, List.map (fun af -> apply_sub_atomic_formula af subs) afs) *)
  (* | NotEqOp (name, af) ->
    NotEqOp (name, apply_sub_atomic_formula af subs) *)
  | Reserved_Keyword_Fail keyword ->
    Reserved_Keyword_Fail keyword
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
  | Comparasion (t1, op1, t2), Comparasion (t3, op2, t4) when op1 = op2 ->
    begin match unify t1 t3 subs with
    | Some subs' -> unify t2 t4 subs'
    | None -> None
    end 
  | NotEqOp (name1, af1), NotEqOp (name2, af2) when name1 = name2 ->
    unify af1 af2 subs     
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
  (* | NotEqOp (name1, afs1), NotEqOp (name2, afs2) when name1 = name2 ->
    unify_atomic_formulas_list afs1 afs2 subs *)
  | FunctionForm_Is (t1, t2), FunctionForm_Is (t3, t4) ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end
  (* | NotEqOp_1 (name1, af1), NotEqOp_1 (name2, af2) when name1 = name2 ->
      unify_atomic af1 af2 subs *)
  (* | Comparasion (t1, op1, t2), Comparasion (t3, op2, t4) when op1 = op2 ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end *)
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
  
(* Helper function to evaluate arithmetic expressions with variable substitution *)
let rec eval_arithmetic subs = function
  | Variable v ->
    begin match Hashtbl.find_opt subs v with
      | Some (Constant c) -> int_of_string c
      | Some (Variable _ as var) -> eval_arithmetic subs var  (* Recursive for chained variables *)
      | None -> failwith ("Unbound variable encountered in arithmetic expression: " ^ v)
      | _ -> failwith ("Non-integer variable encountered in arithmetic expression: " ^ v)
    end
  | Constant c -> int_of_string c
  | Arithmetic (t1, op, t2) ->
    let v1 = eval_arithmetic subs t1 in
    let v2 = eval_arithmetic subs t2 in
    begin match op with
      | "plus" -> v1 + v2
      | "minus" -> v1 - v2
      | "mult" -> v1 * v2
      | "div" -> if v2 = 0 then failwith "Division by zero" else v1 / v2  (* Add check for division by zero *)
      | _ -> failwith "Unsupported arithmetic operation"
    end
  | _ -> failwith "Unsupported term in evaluation"


(* Helper function to evaluate comparison expressions *)
let rec eval_comparison subs = function
  | Variable v ->
    begin match Hashtbl.find_opt subs v with
      | Some (Constant c) -> int_of_string c
      | Some (Variable _ as var) -> eval_comparison subs var
      | None -> failwith ("Unbound variable in comparison expression: " ^ v)
      | _ -> failwith ("Invalid term for comparison evaluation")
    end
  | Constant c -> int_of_string c
  | Arithmetic _ as expr -> eval_arithmetic subs expr
  | Comparasion(t1,op,t2) ->
    let v1 = eval_comparison subs t1 in 
    let v2 = eval_comparison subs t2 in 
    begin match op with
      | "equal_to" -> if v1=v2 then 1 else 0
      | "not_equalto" -> if  v1 <> v2 then 1 else 0
      | "greaterthan" -> if v1 > v2 then 1 else 0
      | "lessthan" -> if v1 < v2 then  1 else 0
      | "greaterthan_equal_to" -> if v1 >= v2 then 1 else 0
      | "lessthan_equal_to" -> if v1 <= v2 then 1 else 0
      | _ -> failwith "Unsupported comparison operation"
    end
  | _ -> failwith "Unsupported term in evaluation"  

let rec solve goals program =
  match goals with
  | [] -> true
  | g::gs ->
      match g with
      | NotEqOp(name, args) ->  (* Handling for negated atomic formula *)
        let negated_goal = FunctionForm(name, [args])  in 
        if solve [negated_goal] program then
          false  (* If the negated goal is solvable, return false for this branch *)
        else
          solve gs program  (* If the negated goal is not solvable, continue with remaining goals *)
      | _ -> 
        program |> List.exists (fun rule ->
          match rule with
          | Fact f -> (match unify_atomic g f (Hashtbl.create 10) with
                      | Some subs -> solve (apply_subs gs subs) program
                      | None -> 
                        List.iter (fun goal -> print_endline (Ast_print.string_of_atomic_formula goal)) goals;
                        print_newline();
                        false)
          | Rule (head, body) -> (match unify_atomic g head (Hashtbl.create 10) with
                                  | Some subs -> 
                                    let (processed_body, new_subs) = process_body body subs program in
                                    solve (apply_subs (processed_body @ gs) new_subs) program
                                  | None -> 
                                    List.iter (fun goal -> print_endline (Ast_print.string_of_atomic_formula goal)) goals;
                                    print_newline();
                                    false)
          )

(* Process each atomic formula's term list to evaluate arithmetic operations *)
and process_body body subs =
  List.fold_left (fun (acc, subs') af ->
      match af with
      | FunctionForm(name, terms) ->
          let (new_terms, new_subs) = process_terms terms subs' in
          (FunctionForm(name, new_terms) :: acc, new_subs)
      | NotEqOp(name,terms) -> 
        let (new_terms, new_subs) = process_terms terms subs' in
          (NotEqOp(name, new_terms) :: acc, new_subs)    
      | FunctionForm_Is(t1, t2) when is_arithmetic t2 ->
          let result = eval_arithmetic subs' t2 in
          Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
          (acc, subs')  (* Don't add back, just update subs *)
      | FunctionForm_Is(t1, t2) when is_comparasion t2 ->
        let result = eval_comparison subs' t2 in
        (* let result_str = string_of_bool result in *)
        let result_final =  if result=1 then true else false in 
        Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_bool result_final));
            (acc, subs') (* Don't add back, just update subs with the comparison result *)
      | FunctionForm_Is(t1,t2) when is_list t2->
          Hashtbl.add subs' (Ast_print.string_of_term t1) t2;
          (acc, subs')  (* Don't add back, just update subs with the list *) 
      (* | FunctionForm_Is(t1,t2) when is_function t2 -> *)
      | FunctionForm_Is(t1,t2) when is_var t2 ->
        let result = eval_arithmetic subs' t2 in
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
              (acc, subs')
      |  FunctionForm_Is(t1,t2) when is_cons t2 ->
        let result = eval_arithmetic subs' t2 in
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
              (acc, subs')
      (* | NotEqOp(operator,atomic_formulas) ->
        let result = solve atomic_formulas program in 
        if result then failwith "NotEqOp should can not be unified"; *)

    ) ([], subs) body |> fun (body', subs') -> (List.rev body', subs')

(* Process terms in an atomic formula's term list, evaluating arithmetic operations *)
and process_terms terms subs =
  List.fold_right (fun term (acc, subs') ->
      match term with
      | Arithmetic(t1, op, t2) ->
          let result = eval_arithmetic subs' (Arithmetic(t1, op, t2)) in
          (Constant (string_of_int result) :: acc, subs')
      | other -> (other :: acc, subs')
    ) terms ([], subs)

(* Evaluate if a term is an Arithmetic operation for conditional checks *)
and is_arithmetic = function
  | Arithmetic(_, _, _) -> true
  | _ -> false

and is_comparasion = function
  | Comparasion(_, _, _) -> true
  | _ -> false

and is_list = function
  | Prolist(_) -> true
  | Prolist_2(_,_) -> true
  | _ -> false

and is_function = function
  | FunctionTerm(_,_) -> true
  | _ -> false

and is_var = function
  | Variable _ -> true
  | _ -> false

and is_cons = function
  | Constant _  -> true
  | _ -> false 


let prompt () = print_string "?- "; flush stdout

let _ =
  let env = ref [] in  (* Environment to store facts and rules *)
  try
    let lexbuf = Lexing.from_channel stdin in
    prompt ();  (* Initial prompt for input *)
    while true do
      try
        let result = Parser.program Lexer.token lexbuf in
        let (clauses, goals) = result in
        
        (* Update the environment with new clauses *)
        env := !env @ clauses;

        if List.length clauses = 0 && List.length goals = 0 then
          raise Exit
        else begin
          print_tree result;  (* Assuming print_tree is correctly implemented to display the result *)
          print_newline ();

          (* Process goals if any *)
          if List.length goals > 0 then begin
            let solved = solve goals !env in
            print_endline (if solved then "Yes" else "No");
           
            (* print_endline "Current Substitutions:"; *)
            (* Hashtbl.iter (fun k v -> Printf.printf "%s -> %s\n" k (Ast_print.string_of_term v)) subs; *)
          end;
          flush stdout;
        end;
        prompt ();  (* Prompt for more input after processing *)
      with
      | Parsing.Parse_error -> 
        print_endline "Syntax error";
        Lexing.flush_input lexbuf;  (* Skip bad part of input before continuing *)
        prompt ();
      | Failure err -> 
        print_endline ("Error: " ^ err);
        prompt ();
    done
  with Exit -> print_endline "Exiting.";  (* Proper exit message *)
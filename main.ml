open Lexing
open Ast
open Parser
open Ast_print

type substitution = (string, term) Hashtbl.t

module StringSet = Set.Make(String)


let rec sub_term term subs =
  match term with
  | Variable v -> (try Hashtbl.find subs v with Not_found -> term)
  | Constant c -> Constant c
  | FunctionTerm (f, args) -> FunctionTerm (f, List.map (fun arg -> sub_term arg subs) args)
  | Arithmetic (t1, op, t2) -> Arithmetic (sub_term t1 subs, op, sub_term t2 subs)
  | Prolist terms -> Prolist (List.map (fun t -> sub_term t subs) terms)
  | Prolist_2 (list1, list2) -> Prolist_2 (List.map (fun t -> sub_term t subs) list1, List.map (fun t -> sub_term t subs) list2)
  | Comparasion (t1, op, t2) ->
    Comparasion (sub_term t1 subs, op, sub_term t2 subs)
 


let rec sub_af af subs =
  match af with
  | FunctionForm (name, terms) ->
    FunctionForm (name, List.map (fun term -> sub_term term subs) terms)
  | FunctionForm_Is (t1, t2) ->
    FunctionForm_Is (sub_term t1 subs, sub_term t2 subs)
  | NotEqOp (name, afs) ->
    NotEqOp (name, List.map (fun af -> sub_term af subs) afs)
  (* | NotEqOp (name, af) ->
    NotEqOp (name, sub_term af subs) *)
  | Reserved_Keyword_Fail keyword ->
    Reserved_Keyword_Fail keyword
  (* | Exclaim message ->
    Exclaim message *)


let apply_subs goals subs =
  List.map (fun goal -> sub_af goal subs) goals



let rec unify term1 term2 subs =
  match (term1, term2) with
  | Variable v, t | t, Variable v ->
    Hashtbl.add subs v t; Some subs
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
  (* | NotEqOp (name1, af1), NotEqOp (name2, af2) when name1 = name2 ->
    unify af1 af2 subs      *)
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
    unify_lists afs1 afs2 subs 
  | FunctionForm_Is (t1, t2), FunctionForm_Is (t3, t4) ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end
  (* | NotEqOp (name1, af1), NotEqOp (name2, af2) when name1 = name2 ->
      unify af1 af2 subs *)
  (* | Comparasion (t1, op1, t2), Comparasion (t3, op2, t4) when op1 = op2 ->
      begin match unify t1 t3 subs with
      | Some subs' -> unify t2 t4 subs'
      | None -> None
      end *)
  | Reserved_Keyword_Fail kw1, Reserved_Keyword_Fail kw2 when kw1 = kw2 -> Some subs
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



let rec collect_vars_term acc term =
  match term with
  | Variable v -> StringSet.add v acc
  | FunctionTerm (_, args) ->
    List.fold_left collect_vars_term acc args
    (* List.fold_left collect_vars_term acc args2 *)
  | Arithmetic (t1, _, t2) | Comparasion (t1, _, t2) ->
    collect_vars_term (collect_vars_term acc t1) t2
  | Constant _ -> acc
  
  (* Collect variables from an atomic formula *)
let rec collect_vars_atomic_formula acc af =
  match af with
  | FunctionForm (_, terms) | NotEqOp (_, terms) ->
    List.fold_left collect_vars_term acc terms
  (* | FunctionForm_Is (t1, t2) ->
    collect_vars_term (collect_vars_term acc t1) t2
  | Reserved_Keyword_Fail _ | Exclaim _ -> acc   *)

let rec resolve_final_value subs var =
  match Hashtbl.find_opt subs var with
  | Some (Variable v) -> resolve_final_value subs v  
  | Some value -> value  
  | None -> Variable var  

let print_subs_table subs =
  Hashtbl.iter (fun key value ->
    let final_value = resolve_final_value subs key in  (* Resolve to final value *)
    Printf.printf "%s -> %s\n" key (Ast_print.string_of_term final_value)
  ) subs
    

let eval_list subs ts =
  let evaluated_terms = List.map (eval_arithmetic subs) ts in
  evaluated_terms    

let rec solve goals program =
  let initial_vars = List.fold_left collect_vars_atomic_formula StringSet.empty goals in
  let rec solve_goals goals subs =
    match goals with
    | [] -> Some subs  
    | g::gs ->
      let (processed_goals, new_subs) = process_body [g] subs in
      match processed_goals with
      | processed_g :: _ ->
        begin match processed_g with
        | FunctionForm_Is(_, _) -> solve_goals gs new_subs
        | NotEqOp(name, args) ->
          let negated_goal = FunctionForm(name, args) in
          if solve_goals [negated_goal] new_subs <> None then None
          else solve_goals gs new_subs
        |  Exclaim(t) ->   
          Some new_subs  
        | Reserved_Keyword_Fail(_) ->
          None  
        | _ ->
          program |> List.fold_left (fun acc rule ->
            match acc with
            | Some subs -> Some subs  
            | None ->
              match rule with
              | Fact f -> 
                (match unify_atomic processed_g f new_subs with
                | Some newer_subs -> solve_goals gs newer_subs
                | None -> None)
              | Rule (head, body) ->
                (match unify_atomic processed_g head new_subs with
                | Some newest_subs -> 
                  let (processed_body, processed_subs) = process_body_2 body newest_subs in
                  solve_goals (processed_body @ gs) processed_subs  
                | None -> None)
          ) None
        end
      | [] -> None  
  in
  let final_subs = solve_goals goals (Hashtbl.create 10) in
  match final_subs with
  | Some subs ->
    print_endline "Final Variable Bindings:";
    StringSet.iter (fun var ->
    match Hashtbl.find_opt subs var with
    | Some value ->
      (try
        let result = eval_arithmetic subs value in
        Printf.printf "%s -> %d\n" var result
      with
      | Failure msg -> Printf.printf "Error evaluating %s: %s\n" var msg)
    | None -> Printf.printf "%s is unbound\n" var
    ) initial_vars;
    true
  | None -> false

and process_body_2 body subs =
  List.fold_left (fun (acc, subs') af ->
    match af with
    | FunctionForm(name, terms) ->
      let (new_terms, new_subs) = process_terms_with_unique_vars terms subs' in
      (FunctionForm(name, new_terms) :: acc, new_subs)
    | NotEqOp(name, terms) ->
      let (new_terms, new_subs) = process_terms_with_unique_vars terms subs' in
      (NotEqOp(name, new_terms) :: acc, new_subs)
    | FunctionForm_Is(t1, t2) ->
      let (new_t1, new_subs1) = process_terms_with_unique_vars [t1] subs' in
      let (new_t2, new_subs2) = process_terms_with_unique_vars_2 [t2] new_subs1 in
      (FunctionForm_Is(List.hd new_t1, List.hd new_t2) :: acc, new_subs2)
    | other -> (other :: acc, subs')  
  ) ([], subs) body |> fun (body', subs') -> (List.rev body', subs')

and process_terms_with_unique_vars terms subs =
  List.fold_right (fun term (acc, subs') ->
    match term with
    | Variable v ->
        let new_var = unique_var subs' v in
        (Variable new_var :: acc, subs')  
    | Prolist_2 (t1, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars t1 subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars t2 subs_t1 in
      (Prolist_2 (new_t1, new_t2) :: acc, subs_t2)
    | FunctionTerm (f, ts) ->
      let (new_ts, new_subs) = process_terms_with_unique_vars ts subs' in
      (FunctionTerm (f, new_ts) :: acc, new_subs)
    | Arithmetic (t1, op, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars [t1] subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars [t2] subs_t1 in
      (Arithmetic (List.hd new_t1,op,List.hd new_t2) :: acc, subs_t2)
    | Comparasion (t1, op, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars [t1] subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars [t2] subs_t1 in
      (Comparasion (List.hd new_t1,op,List.hd new_t2) :: acc, subs_t2)
    | Prolist ts ->
      let (new_ts, new_subs) = process_terms_with_unique_vars ts subs' in
      (Prolist new_ts :: acc, new_subs)
    | Any -> (Any :: acc, subs')  
    | Constant c -> (Constant c :: acc, subs') 
  ) terms ([], subs)

and process_terms_with_unique_vars_2 terms subs =
  List.fold_right (fun term (acc, subs') ->
    match term with
    | Variable v ->
      (try
        let result = eval_arithmetic subs' term  in
        (Constant (string_of_int result) :: acc, subs')
      with _ ->
        let new_var = unique_var subs' v in
        (Variable new_var :: acc, subs'))  
    | Prolist_2 (t1, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars_2 t1 subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars_2 t2 subs_t1 in
      (Prolist_2 (new_t1, new_t2) :: acc, subs_t2)
    | FunctionTerm (f, ts) ->
      let (new_ts, new_subs) = process_terms_with_unique_vars_2 ts subs' in
      (FunctionTerm (f, new_ts) :: acc, new_subs)
    | Arithmetic (t1, op, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars_2 [t1] subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars_2 [t2] subs_t1 in
      (Arithmetic (List.hd new_t1,op,List.hd new_t2) :: acc, subs_t2)
    | Comparasion (t1,op, t2) ->
      let (new_t1, subs_t1) = process_terms_with_unique_vars_2 [t1] subs' in
      let (new_t2, subs_t2) = process_terms_with_unique_vars_2 [t2] subs_t1 in
      (Comparasion (List.hd new_t1,op, List.hd new_t2) :: acc, subs_t2)
    | Prolist ts ->
      let (new_ts, new_subs) = process_terms_with_unique_vars_2 ts subs' in
      (Prolist new_ts :: acc, new_subs)
    | Any -> (Any :: acc, subs')  
    | Constant c -> (Constant c :: acc, subs')  
  ) terms ([], subs)


and unique_var subs var =
  if Hashtbl.mem subs var then
    match Hashtbl.find subs var with
    | Constant c -> var  
    | _ -> unique_var subs (var ^ "$")  
  else
    var

and process_body body subs =
  List.fold_left (fun (acc, subs') af ->
    match af with
    | FunctionForm(name, terms) ->
        let (new_terms, new_subs) = process_terms terms subs' in
        (FunctionForm(name, new_terms) :: acc, new_subs)
    | NotEqOp(name,terms) -> 
      let (new_terms, new_subs) = process_terms terms subs' in
        (NotEqOp(name, new_terms) :: acc, new_subs)
    | Reserved_Keyword_Fail(t) -> (Reserved_Keyword_Fail(t)::acc,subs')
    | Exclaim(t1) -> (Exclaim(t1)::acc,subs')
    | FunctionForm_Is(t1, t2) when is_arithmetic t2 ->
        match t2 with
        | Arithmetic(_, _, _) ->
            let result = eval_arithmetic subs' t2 in
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
            (FunctionForm_Is(t1,Constant (string_of_int result)) :: acc, subs')  
        | Comparasion(t1',op, t2') ->
            let result = eval_comparison subs' t2 in
            let result_final =  if result=1 then true else false in 
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_bool result_final));
            (FunctionForm_Is(t1,Constant (string_of_bool result_final)) :: acc, subs')  
        | Prolist ts ->
            let evaluated_terms = eval_list subs' ts in
            let constants = List.map (fun num -> Constant (string_of_int num)) evaluated_terms in
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Prolist(constants));
            (FunctionForm_Is(t1,Prolist(constants)) :: acc, subs')   
        | Constant _ -> 
          let result = eval_arithmetic subs' t2 in
          Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
          (FunctionForm_Is(t1,Constant(string_of_int result)) :: acc, subs')
        | Variable _ -> 
          let result = eval_arithmetic subs' t2 in
          Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
          (FunctionForm_Is(t1,Constant(string_of_int result)) :: acc, subs')
        | _ -> failwith ("Unsupported term for AtomicformulaIS: " ^ Ast_print.string_of_term t2)

    | _ -> (af :: acc, subs')  
  ) ([], subs) body |> fun (body', subs') -> (List.rev body', subs')
  
  
and process_terms terms subs =
    List.fold_right (fun term (acc, subs') ->
        match term with
        | Arithmetic(t1, op, t2) ->
            let result = eval_arithmetic subs' (Arithmetic(t1, op, t2)) in
            (Constant (string_of_int result) :: acc, subs')
        | Comparasion(t1,op, t2) ->
            let v1 = eval_arithmetic subs' t1 in
            let v2 = eval_arithmetic subs' t2 in
            let result = match op with
              | "<" -> v1 < v2
              | ">" -> v1 > v2
              | "=<" -> v1 <= v2
              | "=>" -> v1 >= v2
              | _ -> failwith ("Unsupported comparison operation: " ^ op)
            in (Constant (string_of_bool result) :: acc, subs')
        | Prolist ts ->
            let evaluated_terms = List.map (eval_arithmetic subs') ts in
            let constants = List.map (fun num -> Constant (string_of_int num)) evaluated_terms in
            (Prolist(constants) :: acc, subs')
        | Variable v ->
            (try
              let result = eval_arithmetic subs' (Variable v) in
              (Constant (string_of_int result) :: acc, subs')
            with
            | Failure _ ->
              (Variable v :: acc, subs') ) 
        | other ->
            (other :: acc, subs') 
    ) terms ([], subs)
  
and is_arithmetic = function
  | Arithmetic(_, _, _) -> true 
  | Comparasion(_, _, _) -> true  
  | Prolist _ -> true         
  | Variable _ -> true             
  | Constant _ -> true             
  | _ -> false



let rec process_body_main body subs =
  List.fold_left (fun (acc, subs') af ->
      match af with
      | FunctionForm(name, terms) ->
          let (new_terms, new_subs) = process_terms_main terms subs' in
          (FunctionForm(name, new_terms) :: acc, new_subs)
      | NotEqOp(name,terms) -> 
        let (new_terms, new_subs) = process_terms_main terms subs' in
          (NotEqOp(name, new_terms) :: acc, new_subs)    
      | FunctionForm_Is(t1, t2) when is_arithmetic_1 t2 ->
          let result = eval_arithmetic subs' t2 in
          Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
          (acc, subs')  
      | FunctionForm_Is(t1, t2) when is_comparasion_1 t2 ->
        let result = eval_comparison subs' t2 in
        let result_final =  if result=1 then true else false in 
        Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_bool result_final));
            (acc, subs') 
      | FunctionForm_Is(t1,t2) when is_list_1 t2->
          Hashtbl.add subs' (Ast_print.string_of_term t1) t2;
          (acc, subs')  
      | FunctionForm_Is(t1,t2) when is_var_1 t2 ->
        let result = eval_arithmetic subs' t2 in
            Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
              (acc, subs')
      |  FunctionForm_Is(t1,t2) when is_cons_1 t2 ->
        let result = eval_arithmetic subs' t2 in
        Hashtbl.add subs' (Ast_print.string_of_term t1) (Constant (string_of_int result));
          (acc, subs')
      (* | NotEqOp(operator,atomic_formulas) ->
        let result = solve atomic_formulas program in 
        if result then failwith "NotEqOp should can not be unified"; *)
      | Exclaim(_) -> (acc,subs')
      | Reserved_Keyword_Fail(t) -> (Reserved_Keyword_Fail(t)::acc,subs')  

    ) ([], subs) body |> fun (body', subs') -> (List.rev body', subs')

and is_arithmetic_1 = function
  | Arithmetic(_, _, _) -> true
  | _ -> false
  
and is_comparasion_1 = function
  | Comparasion(_, _, _) -> true
  | _ -> false

and is_list_1 = function
  | Prolist(_) -> true
  | Prolist_2(_,_) -> true
  | _ -> false

and is_function_1 = function
  | FunctionTerm(_,_) -> true
  | _ -> false

and is_var_1 = function
  | Variable _ -> true
  | _ -> false

and is_cons_1 = function
  | Constant _  -> true
  | _ -> false 
      
and process_terms_main terms subs =
  List.fold_right (fun term (acc, subs') ->
      match term with
      | Arithmetic(t1, op, t2) ->
          let result = eval_arithmetic subs' (Arithmetic(t1, op, t2)) in
          (Constant (string_of_int result) :: acc, subs')
      | other -> (other :: acc, subs')
    ) terms ([], subs)



(* Solve function with proper handling of substitutions *)
let rec solve_1 goals program =
  let initial_vars = List.fold_left collect_vars_atomic_formula StringSet.empty goals in

  let rec solve_goals_1 goals subs =
    match goals with
    | [] -> Some subs  
    | g::gs ->
      match g with
      | Reserved_Keyword_Fail(_) ->
        None
      | NotEqOp(name, args) ->
        let negated_goal = FunctionForm(name, args) in
        if solve_goals_1 [negated_goal] subs <> None then None
        else solve_goals_1 gs subs
      | FunctionForm_Is(t1,t2) ->
        let (process_body,new_subs) = process_body [g] subs in
        Some new_subs
      |  Exclaim(t) ->   
        Some subs
      | _ ->
        program |> List.fold_left (fun acc rule ->
          match acc with
          | Some subs -> Some subs  (* If already solved, skip further processing *)
          | None ->
            match rule with
            | Fact f -> 
              (match unify_atomic g f subs with
              | Some new_subs -> solve_goals_1 gs new_subs
              | None -> None)
            | Rule (head, body) ->
              (match unify_atomic g head subs with
              | Some subs -> 
                let (processed_body, new_subs) = process_body_1 body subs in
                solve_goals_1 (processed_body @ gs) new_subs
              | None -> None)
        ) None
  in
  let final_subs = solve_goals_1 goals (Hashtbl.create 10) in
  match final_subs with
  | Some subs ->
    print_newline();
    print_endline "Final Variable Bindings:";
    StringSet.iter (fun var ->
      let final_value = resolve_final_value subs var in
      Printf.printf "%s -> %s\n" var (Ast_print.string_of_term final_value)
    ) initial_vars;
    true
  | None -> false

  


and process_body_1 goals subs =
  List.fold_left (fun (acc, subs') goal ->
    match goal with
    | FunctionForm(name, terms) ->
      let new_terms, new_subs = process_terms_main terms subs' in
      (FunctionForm(name, new_terms) :: acc, new_subs)
    | NotEqOp(name,terms) -> 
      let (new_terms, new_subs) = process_terms_main terms subs' in
        (NotEqOp(name, new_terms) :: acc, new_subs)    
    | _ -> (goal :: acc, subs')  (* Include other goal types as needed *)
  ) ([], subs) goals |> fun (body', subs') -> (List.rev body', subs')  
    

(* Stdlib.stdout *)

let prompt () = print_string "?- "; flush Stdlib.stdout


let _ =
  let env = ref [] in  (* Environment to store facts and rules *)
  try
    let lexbuf = Lexing.from_channel Stdlib.stdin in
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
            let solved = solve_1 goals !env in
            print_endline (if solved then "Yes" else "No");
           
            (* print_endline "Current Substitutions:"; *)
            (* Hashtbl.iter (fun k v -> Printf.printf "%s -> %s\n" k (Ast_print.string_of_term v)) subs; *)
          end;
          flush Stdlib.stdout;
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
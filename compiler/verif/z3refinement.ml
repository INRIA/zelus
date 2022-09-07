(* Z3 interface to type check refinement types*)

(*Open Z3 interface*)
open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector
open Z3enums

exception Z3FailedException of string

(*Open Zelus Interface*)
open Zident
open Global
open Modules
open Deftypes
open Ztypes
open Typerrors

open Zmisc
open Zlocation
open Format
open Zelus

open List
open Hashtbl


(*
type variable = 
  { 
    name:         string;
    refinement_t: expr;
  }
*)

(*TODO :Change this to a Z3 vc_gen_expression type, then add stuff by AND-ing it on the head *)
(*let z3env = ref []*)

let debug message =
  (* log debug message *)
  if !ref_verbose then (Printf.printf "[DEBUG] : %s\n" message) 


type env_structure =
(*
      environment to hold
      exp_env : local vc_gen_expression environment
      var_env : local variable environment
*)
{
  exp_env : expr list ref;
  var_env : (string, expr) Hashtbl.t;
}

type custom_t = {
(*
      string base_type;
      string reference_variable;
      z3_expression Phi(reference_variable);
*)
  base_type : string;
  reference_variable : string;
  phi : exp;
}

let add_constraint ({ exp_env = env; var_env = v}) premise = 
(*
    env     -> environment (list of z3 vc_gen_expressions)
    premise -> z3 vc_gen_expression
    
    Add premise to end of environment list
*)
   env := premise::(!env) 

(*
type z3env =
{
  scope: variable list;
  prev:  z3env;
}*)

type function_desc = 
(*
    Function object definition
*)
{
  argument_constraints: expr list;
  variable_maps: (string, custom_t) Hashtbl.t;
  argument_list: string list;
  creation_env: env_structure;
}

(*TODO: make two variants for refinement functions and non-refinement functions *)
let function_space =
(*Hash table to store functions given a function name*)
    let function_table : ((string, function_desc ) Hashtbl.t) =  (Hashtbl.create 1)
    in ref function_table

let type_space =
    let type_table : ((string, custom_t) Hashtbl.t) = (Hashtbl.create 1)
    in ref type_table

let erefinement2customt erefinement ctx env typenv =
  match erefinement.desc with
  | Erefinement(t,e) -> (
    debug(Printf.sprintf "Erefinement e2t");
    match (snd t).desc with
    | Etypeconstr(name, t_exp_list) -> 
      (
        match name with
          | Lident.Name(basetype) -> debug(basetype); debug(fst t); { base_type = basetype;
             reference_variable = fst t;
             phi = e; }
      ) 
    | _ -> debug(Printf.sprintf "Unknown e2t"); { base_type = "";
             reference_variable = "";
             phi = e; } 
  )
let add_type name t_add =
(*
    name  -> type name
    t_add -> Erefinement object

    Adds a new type to type space
*)
  Hashtbl.add (!type_space) name t_add 

let add_function name f_add =
(*
    name  -> fucntion name
    f_add -> function_desc object

    Adds a  new function to function space
*)
  Hashtbl.add (!function_space) name f_add 

type stream_desc =
(*
    Stream object definitions
*)
{
  initialization_var:   expr;
  application_function: string;
  return_exp : expr;
  refinement_exp : expr list;
}
let stream_space =
(* Hash table to store streams given a stream name*)
  let stream_table : ((string, stream_desc) Hashtbl.t) = (Hashtbl.create 1)
in ref stream_table

let add_stream name stream_add =
(*
    name -> stream name
    stream_add -> stream desc object

    Add a new stream to stream space
*)
  Hashtbl.add (!stream_space) name stream_add

let proof_error_count = ref 0 (* count for proof errors *)
(**
(*Define refinement type vc_gen_pattern*)
type z3op =
    | Z3eval of string * string * exp * exp
    
type z3exp =
    | Z3int of int
    | Z3real of float

(* convert immeiate type to respective string *)
let immediate = function
  | Ebool(b) -> if b then "true" else "false" 
  | Eint(i) -> Printf.sprintf "%d" i
  | Efloat(i) -> Printf.sprintf "%f" i
  | Echar(c) -> Printf.sprintf "'%c'" c
  | Estring(c) -> Printf.sprintf "'%s'" c
  | Evoid -> Printf.sprintf ""
  
let qualident { Lident.qual = m; Lident.id = s } =
  Printf.sprintf "%s.%s" m s
 
let print_elt f e = 
	print_string (Printf.sprintf "List exp: '%s'\n" (f e)) 
	
let type_exp typ = 
	match typ with
	  | Vconst(i) -> immediate i (* constant *)
	  | Vconstr0(ln) -> qualident ln (* constructor *)
	  | Vabstract(ln) -> qualident ln (* no implementation is given *)

let qualid_exp typ = 
	match typ with
	  | None  -> "None" (* constant *)
	  | Some(ln) -> qualident ln (* constructor *)
  
let print_info info =
	(*print_string (Printf.sprintf "Value typ: '%s' \n" (List.hd (info.value_typ.typ_vars)));*)
	print_string (Printf.sprintf "Value static: '%b' \n" (info.value_static));
	(*print_string (Printf.sprintf "Value caus: '%s' \n" info.value_caus);
	print_string ("Value init: \n");
	print_string (String.concat " " (List.map (Printf.sprintf "'%s'") info.value_init));*)
	print_string (Printf.sprintf "Value code exp: '%s' \n"  ( type_exp info.value_code.value_exp));
	print_string (Printf.sprintf "Value code name: '%s' \n" ( qualid_exp info.value_code.value_name)); "Info"
	
(* parse input vc_gen_expression into string and redirect to Z3 solver *)
let rec parse_vc_gen_expression e = 
  match e.e_desc with
    | Elocal n -> print_string "Elocal\n"; "1.0"
    | Eglobal { lname = ln } -> print_string "Eglobal\n"; let var_name = Lident.modname ln in print_string var_name; print_newline(); 
    let var2 =
    	try 
    	   let { info = info } = Modules.find_value ln in print_info info
    	with 
    	   | Not_found -> "No info" in
    var_name
    | Eop(op, e_list) -> print_string "Eop\n"; "1.0"
    | Elast x -> print_string "Elast\n"; "1.0"
    | Econstr0(ln) -> print_string "Econstr0\n"; "1.0"
    | Econst c -> print_string "Econst\n"; immediate c
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) ->
       print_string (Printf.sprintf "App inline: '%b'\n" i);
       print_string (Printf.sprintf "App stateful: '%b'\n" r);
       (*print_string (Printf.sprintf "Exp parsing: '%s' \n" (parse_vc_gen_expression e));
       print_string "Map start\n";
       let dummy = List.map (print_elt parse_vc_gen_expression) e_list in
       print_string "Eapp\n"; "1.0"*)
       let vc_gen_operator = Printf.sprintf "'%s'" (parse_vc_gen_expression e) in
       let exp_list = List.map parse_vc_gen_expression e_list in
       List.hd (List.tl exp_list)
    | Econstr1(ln, e_list) ->
        print_string "Econstr1\n"; "1.0"
    | Etuple(e_list) ->
        print_string "Etuple\n"; "1.0"
    | Erecord_access(e, field) ->
        print_string "Erecord_access\n"; "1.0"
    | Erecord(ln_e_list) ->
        print_string "Erecord\n"; "1.0"
    | Erecord_with(e, ln_e_list) ->
       print_string "Erecord_with\n"; "1.0"
    | Elet(l, e) ->
        print_string "Elet\n"; "1.0"
    | Eblock(b, e) ->
       print_string "Eblock\n"; "1.0"
    | Etypeconstraint(e, typ) ->
        print_string "Etypeconstraint\n"; "1.0"
    | Eseq(e1, e2) ->
        print_string "Eseq\n"; "1.0"
    | Eperiod(p) ->
        print_string "Eperiod\n"; "1.0"
    | Ematch(total, e, match_handler_list) ->
        print_string "Ematch\n"; "1.0"
    | Epresent(present_handler_list, opt_e) ->
        print_string "Epresent\n"; "1.0" 
     

let evaluate name ty e1 e2 : bool =
	Printf.printf "Running Zelus evaluation verifier \n";
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let var = Real.mk_numeral_s ctx e2 in
	let threshold = Real.mk_numeral_s ctx e1 in
	let phi variable refinement =
		Arithmetic.mk_ge ctx variable refinement in
	let correct = (Boolean.mk_and ctx
			[(phi var threshold);]) in
	let solver = (mk_solver ctx None) in
	let s = (Solver.add solver [correct]) in
	let q = check solver [] in
	Printf.printf "Solver says: %s\n" (string_of_status q) ;
    	if q == SATISFIABLE then true
    	else 
	     raise (Z3FailedException "Z3 verification failed")
	     
let rec prove_satisfiability op : bool =
	match op with
	| Z3eval(var, ty, e1, e2) -> 
	let arg = parse_vc_gen_expression e1 in
	let arg2 = parse_vc_gen_expression e2 in
	print_string arg; print_newline(); print_string arg2; print_newline();
	evaluate var ty (arg) (arg2)
*)
exception TestFailedException of string

let print_assignments m = 
(*
    m -> z3 model

    Print counterexamples found for a given z3 model
*)
  let decls = (Model.get_decls m) in
    List.iter (fun a -> (match (Model.get_const_interp m a) with
      | Some(e) -> Printf.printf "\t%s: %s\n" (Symbol.get_string (FuncDecl.get_name a)) 
          (if (Arithmetic.is_real e) then (Arithmetic.Real.to_decimal_string e 5) else (Expr.to_string e))
      | None -> ()
    )) decls

let build_z3_premise ctx ({exp_env = l; var_env = v}) =
(*
    ctx -> z3 context
    l   -> list of z3 vc_gen_expressions

    Returns the conjunctions of z3 vc_gen_expressions in list l
*)
  match !l with
  | [] -> Boolean.mk_true ctx
  | _ -> Boolean.mk_and ctx !l

(* let check_arg_list f arg_list =
(*
  Check that input arguments agree with function definition
*)
  if List.len (f.argument_list) != List.len (arg_list) then
    Printf.printf "Function expected different number of arguments";
    raise Z3FailedException
  else 
    let rec validate_args l1 l2 = *)

let print_env_list premise =
(*
  premise -> list of z3 vc_gen_expressions
    
  Print list of z3 vc_gen_expressions
*)
  debug (Printf.sprintf "vc_gen_expression = %s ; " (Expr.to_string premise))

let print_env ({exp_env = env; var_env = v}) = 
(*
  env -> vc_gen_expression environment
  v   -> variable environment
*)
  debug (Printf.sprintf ("vc_gen_expression environment : \n"));
  List.iter print_env_list !env; debug("")

let print_function_temp n f =
(*
  temporary function used for debugging, I will delete it later

  same thing as print_function but it is defined earlier
*)
  if !ref_verbose then (
      debug("");
      Printf.printf "Function: %s\n" n;
      Printf.printf "Argument_constraints:\n";
      List.iter (fun a -> (Printf.printf "%s; " (Expr.to_string a))) f.argument_constraints;
      Printf.printf "\n";
      Printf.printf "Variable map:\n";
      Hashtbl.iter (fun a b -> (Printf.printf "%s:%s; " a b.base_type)) f.variable_maps;
      Printf.printf "\n";
      Printf.printf "Argument list:\n";
      List.iter (fun a -> (Printf.printf "%s; " a)) f.argument_list;
      Printf.printf "Creation environment\n";
      print_env f.creation_env
  )

let make_void ctx =
  let void_sort = Sort.mk_uninterpreted_s ctx "NULL" in
  Expr.mk_fresh_const ctx "NULL" void_sort

let sort2type sort_enum =
  match sort_enum with
  |	BOOL_SORT -> "bool"
  |	INT_SORT -> "int"
  |	REAL_SORT -> "float"
  |	FLOATING_POINT_SORT -> "float"
  |	CHAR_SORT -> "char"
  |	_ -> "NULL"

let z3_proof ctx env vc constraints =
(*
  ctx         -> z3 context
  env         -> environment (list of z3 vc_gen_expression)
  constraints -> z3 constraints to solve

  Attempts to prove that ! ( environement expreession -> constraints)

  Raises an exception if proof fails or resumes the operations
*)
  debug (Printf.sprintf "\n--- Z3 SOLVE ---\n");
  debug (Printf.sprintf "environment:\n");
  print_env env; 
  debug (Printf.sprintf "constraint:\n");
  debug (Printf.sprintf "%s\n" (Expr.to_string constraints));
  debug (Printf.sprintf "--- Z3 SOLVE ---\n\n");
  try (
  let solver = (mk_solver ctx None) in
  (Printf.printf "Proving constraint: %s\n" (Expr.to_string vc));
  let s = (Solver.add solver [vc]) in
  let q = check solver [] in
  (if q == SATISFIABLE then
    (Printf.printf "\027[31mCounterexample found:\n";
    (let m = (get_model solver) in    
      		match m with 
          | None -> ()
		      | Some (m) -> 
	  	      (*Printf.printf "Model: \n%s\n" (Model.to_string m);*)
            print_assignments m;
      let err_msg = Printf.sprintf "Could not prove: %s\n\027[0m" (Expr.to_string constraints) in
      proof_error_count := !proof_error_count + 1;
      raise (TestFailedException err_msg)))
  else
    (Printf.printf "\027[32mPassed\027[0m\n";));
    add_constraint env constraints
  )
  with 
  | TestFailedException(msg) -> Printf.printf "%s" msg

let z3_solve ctx env constraints = 
(*
  ctx         -> z3 context
  env         -> environment (list of z3 vc_gen_expression)
  constraints -> z3 constraints to solve

  Attempts to prove that ! ( environement expreession -> constraints)

  Raises an exception if proof fails or resumes the operations
*)
  let vc = Boolean.mk_not ctx (Boolean.mk_implies ctx 
  (build_z3_premise ctx env)
  (constraints)) in
  z3_proof ctx env vc constraints


let z3_solve_stream ctx env stream_c constraints =
(*
  ctx         -> z3 context
  env         -> environment (list of z3 vc_gen_expression)
  stream_c -> z3 constraints derived from stream
  constraints -> stream type we want to prove

  Attempts to prove that 
  
  ! ( (env::stream_c[0] -> refinement_expr ) and ( env::stream_c[1] -> refinment_expr))

  Raises an exception if proof fails or resumes the operations
*)
  match stream_c with
    | stream1 :: stream2 :: [] -> 
      let env1 = stream1::(!(env.exp_env)) in
      let env2 = stream2::(!(env.exp_env)) in
      let vc = Boolean.mk_not ctx (Boolean.mk_and ctx 
                                    [(Boolean.mk_implies ctx 
                                        (Boolean.mk_and ctx env1)
                                        (constraints));
                                      (Boolean.mk_implies ctx 
                                        (Boolean.mk_and ctx env2)
                                        (constraints)) 
                                      ]) in
      z3_proof ctx env vc constraints

let create_z3_var_typed ctx ({exp_env = e ; var_env = v}) s basetype : expr =
(*
    ctx -> z3 context
    s   -> variable name

    Create z3 sort with specific basetype with given variable name s
*)
  debug (Printf.sprintf "\n --- CREATE Z3 VAR TYPED : %s --- \n" s);
  (* Look at environment for variable*)
  if (Hashtbl.mem v s) then
    (*if exists return varible*)
      let found_var = Hashtbl.find v s in
      debug (Printf.sprintf "Existing variable, returning %s\n\n" (Expr.to_string found_var));
      found_var
  else
    (*otherwise create a new variable and add to environment*)
    let new_var =  
    (match basetype with
      | "int" -> debug(Printf.sprintf " I will make an int here\n"); Expr.mk_const ctx (Symbol.mk_string ctx s) (Integer.mk_sort ctx)
      | "float" -> debug(Printf.sprintf " I will make a float here\n"); Expr.mk_const ctx (Symbol.mk_string ctx s) (Real.mk_sort ctx)
      (* | "string" -> Printf.printf " I will make a string here\n"; (Expr.mk_const ctx (Symbol.mk_string ctx n.source) (.mk_sort ctx))
      | "char" -> Printf.printf " I will make a char here\n"; (Expr.mk_const ctx (Symbol.mk_string ctx n.source) (.mk_sort ctx))*)
      | "bool" -> debug(Printf.sprintf " I will make a bool here\n"); (Expr.mk_const ctx (Symbol.mk_string ctx s) (Boolean.mk_sort ctx))
      | _ ->  debug (Printf.sprintf " I don't know what to make here\n"); make_void ctx
    ) in
    Hashtbl.add v s new_var;
    debug (Printf.sprintf "New variable, returning %s\n\n" (Expr.to_string new_var));
    new_var

let create_z3_var ctx ({exp_env = e ; var_env = v}) s =
  (*
      ctx -> z3 context
      s   -> variable name
  
      Create generic z3 Real sort with given variable name s
  *)
    create_z3_var_typed ctx ({exp_env = e ; var_env = v}) s "float"

let print_function n f =
(*
    n -> function name
    f -> function description

    Prints all fields in function data structure
*)
  if !ref_verbose then (
    Printf.printf "Function: %s\n" n;
    Printf.printf "Argument_constraints:\n";
    List.iter (fun a -> (Printf.printf "%s; " (Expr.to_string a))) f.argument_constraints;
    Printf.printf "\n";
    Printf.printf "Variable map:\n";
    Hashtbl.iter (fun a b -> (Printf.printf "%s:%s; " a b.base_type)) f.variable_maps;
    Printf.printf "\n";
    Printf.printf "Argument list:\n";
    List.iter (fun a -> (Printf.printf "%s; " a)) f.argument_list;
    Printf.printf "Creation environment\n";
    print_env f.creation_env;
    Printf.printf "\n\n" 
  )

let print_function_environment () =
(*
  Prints all function description in function space
*)
    Hashtbl.iter ( fun n f -> print_function n f ) (!function_space)


let immediate ctx i = 
(*
    ctx -> z3 context
    i   -> immediate type vc_gen_expression

    Converts immediate type vc_gen_expression into z3 sort

    Returns z3 sort
*)
  debug (Printf.sprintf "\n --- CREATE Z3 VAR IMMEDIATE :  --- \n");
  (* Look at environment for variable*)
  match i with
      | Ebool(b) ->  Boolean.mk_val ctx b 
      | Eint(i) -> debug ((Printf.sprintf "Z3 Int %d\n") i); Integer.mk_numeral_s ctx (Printf.sprintf "%d" i)
      (*TODO: in general reals and floating points are not the same*)
      | Efloat(i) -> debug ((Printf.sprintf "Z3 Float %f\n") i); Real.mk_numeral_s ctx (Printf.sprintf "%f" i)
      | Estring(c) -> debug (Printf.sprintf "string: %s\n" c); Expr.mk_const ctx (Symbol.mk_string ctx c) (Real.mk_sort ctx)
      | Echar(c) -> debug (Printf.sprintf "%c" c); Integer.mk_numeral_s ctx "42"
      | Evoid -> debug (Printf.sprintf "void"); make_void ctx
      (* | Evoid -> debug (Printf.sprintf "void"); Boolean.mk_true ctx *)
      | _ -> debug (Printf.sprintf "Ignore immediate \n"); Integer.mk_numeral_s ctx "42"

(* let rec local ctx env typenv l =
   let expr = vc_gen_expression ctx env (List.hd l.l_eq) typenv in
   Printf.printf "%s\n" (Expr.to_string expr) *)

(* and local = 
  { l_rec: is_rec; (* is-it recursive *)
    l_eq: eq list; (* the set of parallel equations *)
    mutable l_env: Deftypes.tentry Zident.Env.t;
    l_loc: location } *)
let rec create_base_var_from_pattern ctx env pat = 
    match pat.p_desc with 
    | Etypeconstraintpat(p,t) ->
      let base_type = 
        (
          match t.desc with
            | Erefinement(lbl, ref_exp) -> 
              (
                match (snd(lbl)).desc with 
                  | Etypeconstr(long_name, _) -> 
                      (
                        match long_name with
                          | Name(s) -> s
                          | Modname(q) -> q.id
                      )
              )
        ) in
      (match p.p_desc with 
      | Evarpat(n) -> debug (Printf.sprintf "Etypeconstraintpat: %s\n" n.source); create_z3_var_typed ctx env n.source base_type
      ) 

and vc_gen_equation_operation ctx env typenv op e_list pat =
    (*
        ctx -> z3 context
        env -> vc_gen_expression environment
        typenv -> typing environment
        op -> vc_gen_operation definition
        e_list -> list of operands
    
        Currently used to type check streams
    *)
    let base_var = create_base_var_from_pattern ctx env pat in 
    let refinement_expr = 
        match pat.p_desc with 
        | Etypeconstraintpat(p, t) ->
          let var_name = (match p.p_desc with 
                           | Evarpat(n) -> n.source) in
          (
            match t.desc with 
             | Erefinement(lbl, ref_exp) ->
                (
                   add_variable_to_table ctx env typenv var_name ref_exp lbl;
                   (vc_gen_substitute (var_name) env ctx typenv)
                )
          )
    in
    match op, e_list with
        | Efby, [e1; e2] ->
            let exp1 = Boolean.mk_eq ctx base_var (vc_gen_expression ctx env e1 typenv) in
            let stream_def = (vc_gen_expression ctx env e2 typenv) in
            let exp2 = Boolean.mk_eq ctx base_var stream_def in
            let base_name = (Expr.to_string base_var) in
            debug(Printf.sprintf "[%s] fby [%s] -> [%s]\n" (Expr.to_string exp1) (Expr.to_string exp2) (Expr.to_string refinement_expr));
            if (expression_contains stream_def base_var) then (
              debug(Printf.sprintf "FBY is recursive");
              (* check if there is better way to identify recursion *)
              let next_step_var = build_next_step_var ctx env base_name (get_expression_sort base_var) in
              let exp3 = Boolean.mk_eq ctx next_step_var stream_def in
              let vc1 = Boolean.mk_implies ctx exp1 refinement_expr in
              let next_refinement_expr = Expr.substitute_one (refinement_expr) (base_var) (next_step_var) in
              debug(Printf.sprintf "Next refinement: %s\n" (Expr.to_string next_refinement_expr));
              let vc2 = Boolean.mk_implies ctx (Boolean.mk_and ctx [refinement_expr; exp3]) (next_refinement_expr) in
              let vc = Boolean.mk_not ctx (Boolean.mk_and ctx [vc1; vc2]) in 
              z3_proof ctx env vc refinement_expr
            ) else (
              (* apply stream typing rule - no recursion*)
              z3_solve_stream ctx env [exp1; exp2] refinement_expr
            ); base_var

        | Eifthenelse, [e1 ; e2; e3] -> 
            debug("Eifthenelse\n");
            let exp1 = vc_gen_expression ctx env e1 typenv in 
            debug(Printf.sprintf "Exp1: %s" (Expr.to_string exp1));
            let exp2 = vc_gen_expression ctx env e2 typenv in
            debug(Printf.sprintf "Exp2: %s" (Expr.to_string exp2));
            let exp3 = vc_gen_expression ctx env e3 typenv in 
            debug(Printf.sprintf "Exp3: %s" (Expr.to_string exp3));
            let exp1_lhs = vc_gen_expression ctx env e1 typenv in
            debug(Printf.sprintf "Exp1_lhs: %s" (Expr.to_string exp1_lhs));
            let exp1_rhs = Expr.substitute_one (refinement_expr) (base_var) (exp2) in
            debug(Printf.sprintf "Exp1_rhs: %s" (Expr.to_string exp1_rhs));
            let exp2_lhs = Boolean.mk_not ctx exp1_lhs in 
            debug(Printf.sprintf "Exp2_lhs: %s" (Expr.to_string exp2_lhs));
            let exp2_rhs = Expr.substitute_one (refinement_expr) (base_var) (exp3) in
            debug(Printf.sprintf "Exp2_rhs: %s" (Expr.to_string exp2_rhs));
            let vc = Boolean.mk_not ctx (
              Boolean.mk_and ctx [ 
                Boolean.mk_implies ctx (exp1_lhs) (exp1_rhs);
                Boolean.mk_implies ctx (exp2_lhs) (exp2_rhs);
              ]
            ) in
            z3_proof ctx env vc refinement_expr;
            base_var

        | _ -> vc_gen_operation ctx env typenv op e_list 

and expression_contains expr var =
      let args = List.map (fun elem -> Expr.to_string elem) (Expr.get_args expr) in
      let var_name = Expr.to_string var in
      debug(Printf.sprintf "Var name: %s \n" var_name);
      List.mem var_name args
      
and vc_gen_equation_expression ctx env e typenv pat =
       (* TODO: check if pat is a tuple or not *)
(*
        ctx    -> z3 context
        env    -> environment (list of z3 vc_gen_expressions)
        desc   -> vc_gen_expression desciption
        loc    -> vc_gen_expression location
        typenv -> typing environment ( Hash table of string = variable name * string = base type)

        Processes zelus vc_gen_expression into z3 vc_gen_expression

        Returns Z3 vc_gen_expression
*)
  match e.e_desc with
  (* | Econst(Evoid) -> Boolean.mk_true ctx *)
  | Eop ( op, e_list) -> debug(Printf.sprintf "Eop pat\n"); vc_gen_equation_operation ctx env typenv op e_list pat
  | Econst(i) ->  debug(Printf.sprintf "Econst\n"); immediate ctx i
  | Eglobal {lname = ln} -> debug(Printf.sprintf "Eglobal\n");Integer.mk_numeral_s ctx "42"
  | Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> debug(Printf.sprintf "Eapp\n");
    (* debug( Printf.sprintf "E: %s\n" (Expr.to_string (vc_gen_expression ctx env e typenv)));
    List.iter (fun a -> debug(Printf.sprintf "E_List: %s \n" (Expr.to_string (vc_gen_expression ctx env a typenv)))) e_list; *)
    let app_expr = vc_gen_operator ctx env typenv (operator_vc_gen_expression_to_string e) e_list in
    debug( Printf.sprintf "App expr: %s\n" (Expr.to_string app_expr)); app_expr
  | Elocal(n) -> debug(Printf.sprintf "Elocal\n");Integer.mk_numeral_s ctx "42"
  | Elet(l, e) -> debug(Printf.sprintf "Elet\n");Integer.mk_numeral_s ctx "42"
  | Econstr0 _ -> debug(Printf.sprintf "Econstr0\n");Integer.mk_numeral_s ctx "42"
  | Econstr1(_ , _) -> debug(Printf.sprintf "Econstr1\n");Integer.mk_numeral_s ctx "42"
  | Elast _ -> debug(Printf.sprintf "Elast\n");Integer.mk_numeral_s ctx "42"
  | Etuple (e_tuple) -> debug(Printf.sprintf "Etuple\n");Integer.mk_numeral_s ctx "42"
  | Erecord_access (_, _) -> debug(Printf.sprintf "Erecord_acess\n");Integer.mk_numeral_s ctx "42"
  | Erecord _-> debug(Printf.sprintf "Erecord\n");Integer.mk_numeral_s ctx "42"
  | Erecord_with (_, _)-> debug(Printf.sprintf "Erecord_with\n");Integer.mk_numeral_s ctx "42"
  | Etypeconstraint (_, _)-> debug(Printf.sprintf "Etypeconstraint\n");Integer.mk_numeral_s ctx "42"
  | Epresent (_, _)-> debug(Printf.sprintf "Epresent\n");Integer.mk_numeral_s ctx "42"
  | Ematch (_, _, _)-> debug(Printf.sprintf "Ematch\n");Integer.mk_numeral_s ctx "42"
  | Eseq ( e1, e2)-> debug(Printf.sprintf ("Eseq : (e1 = %s e2 = %s)\n") (Expr.to_string (vc_gen_expression ctx env e1 typenv)) (Expr.to_string (vc_gen_expression ctx env e2 typenv)));
    Integer.mk_numeral_s ctx "42"
  | Eperiod _-> debug(Printf.sprintf "Eperiod\n"); Integer.mk_numeral_s ctx "42"
  | Eblock (_, _)-> debug(Printf.sprintf "Eblock\n"); Integer.mk_numeral_s ctx "42"  
  | _ -> vc_gen_expression ctx env e typenv

and add_variable_to_table ctx env typenv var_name ref_exp lbl = 
    (match typenv with
    | Some(tbl) -> if (Hashtbl.mem tbl var_name) then
        debug (Printf.sprintf "Variable already exists in typenv\n")
      else
        debug (Printf.sprintf "Creating variable\n");
        Hashtbl.add tbl var_name {base_type = (match (snd(lbl)).desc with
          | Etypeconstr(long_name, _) -> (match long_name with
            | Name(s) -> s
            | Modname(q) -> q.id)
          | _ -> "basetype_not_right"); reference_variable = fst(lbl); phi = ref_exp}
    | None -> ())
(*
and vc_gen_exp_tuple_equation ctx env typenv vars_lhs refvars ref_constraint exp_rhs = 
        match exp.e_desc with
        | *)
and vc_gen_equation ctx env typenv eq =
(*
    ctx    -> z3 context
    env    -> environment (list of z3 vc_gen_expression)
    typenv -> typing environment ( Hash table of string = variable name * string = base type)
    eq     -> zelus vc_gen_equation

    Creates z3 vc_gen_expression from zelus vc_gen_equation

    Returns z3 vc_gen_expression
*)
    match eq.eq_desc with
    | EQeq(p, e) -> debug (Printf.sprintf "EQeq:\n");
        match p.p_desc with
          | Etypeconstraintpat(p1, t) -> (match t.desc with

            | Erefinementlabeledtuple(lbl_ty_list, ref_exp) -> debug (Printf.sprintf "Refinement labeled tuple"); 
                (* Get list of variable names on the LHS *)
                let vars_names = (match p1.p_desc with 
                    | Etuplepat(l) -> (List.map (fun x -> match x.p_desc with
                        | Evarpat(n) -> n.source) l)) in 
                (* Get list of reference variables (important for the later replacement stage) and a list of types to associate with the original variable names *)
                let (vars_refnames, vars_basetypes) = List.split lbl_ty_list in
                Printf.printf "Will perform the following substitutions:\n";
                ignore (List.map2 (Printf.printf "[%s/%s]\n") vars_names vars_refnames);
                let vars_basetypes_strings = (List.map (fun ty-> 
                (match ty.desc with
                   | Etypeconstr(long_name, _) -> (match long_name with
                     | Name(s) -> s
                     | Modname(q) -> q.id)
                   | _ -> "basetype_not_right")) vars_basetypes) in
                let z3vars_ref = (List.map2 (fun x ty -> create_z3_var_typed ctx env x ty) vars_refnames vars_basetypes_strings) in
                (* Make a list of Z3 variables *)
                let z3vars = (List.map2 (fun x ty -> create_z3_var_typed ctx env x ty) vars_names vars_basetypes_strings) in 
                (* Treat the variables separately *)
                (match e.e_desc with
                | Etuple(e_list) -> debug(Printf.sprintf "Tuple with %d elements" (List.length e_list));
                    (* Create equality constraints for each element of tuple *)
                    let right_hand_sides = List.map (fun x -> (vc_gen_expression ctx env x typenv)) e_list in 
                    let equality_constraints = (Boolean.mk_and ctx (List.map2 (Boolean.mk_eq ctx) z3vars right_hand_sides)) in 
                    debug (Printf.sprintf "Equality constraints: %s\n" (Expr.to_string equality_constraints));
                    let ref_constraint = (vc_gen_expression ctx env ref_exp typenv) in
                    debug (Printf.sprintf "Original refinement constraint: %s\n" (Expr.to_string ref_constraint));
                    let assume_constraint = Expr.substitute ref_constraint z3vars_ref z3vars in
                    let test_constraints = Expr.substitute ref_constraint z3vars_ref right_hand_sides in
                    (*debug (Printf.sprintf "Replaced refinement constraint: %s\n" (Expr.to_string new_constraint));*)
                    add_constraint env assume_constraint;
                    z3_solve ctx env test_constraints;
                | Eop(op, e_list) -> debug(Printf.sprintf "operation");
                    (match op, e_list with
                    | Efby, [e1; e2] -> (
                            (* Proving let rec x:{v:t | phi} = e1 fby e2 requires:
                                    * phi[x/v] => phi[e1/v] AND
                                    * phi[x/v] => phi[e2/v]
                                to be true at ALL times, which essentially means we need to DISprove the negation.
                            *)
                            match (e1.e_desc, e2.e_desc) with
                            | (Etuple(e1_list), Etuple(e2_list)) -> debug (Printf.sprintf "Found a tuple fby tuple!");
                                (* Parses e1 and e2 into Z3 expressions *)
                                let e1_exps = List.map (fun x -> (vc_gen_expression ctx env x typenv)) e1_list in 
                                let e2_exps = List.map (fun x -> (vc_gen_expression ctx env x typenv)) e2_list in
                                (Printf.printf "("); (ignore (List.map (fun x -> (Printf.printf "%s," (Expr.to_string x) )) e1_exps)); (Printf.printf ") fby ");
                                (Printf.printf "("); (ignore (List.map (fun x -> (Printf.printf "%s," (Expr.to_string x) )) e2_exps)); (Printf.printf ")\n");
                                (* Parses phi into a Z3 expression *)
                                let ref_constraint = (vc_gen_expression ctx env ref_exp typenv) in
                                (* Gets phi[x/v] *)
                                let ref_replaced_constraint = Expr.substitute ref_constraint z3vars_ref z3vars in
                                (* Gets "next step" variables, or those associated with e2 *)
                                (*let next_step_vars = List.map2 (fun x ty -> (create_z3_var_typed ctx env (Printf.sprintf "%s_next" x) ty)) vars_names vars_basetypes_strings in*)
                                (*
                                let exps1 = List.map2 (Boolean.mk_eq ctx) z3vars e1_exps in
                                let exps3 = List.map2 (Boolean.mk_eq ctx) next_step_vars e2_exps in*)
                                (* vc1: 
                                let vc1 = Boolean.mk_implies ctx (Boolean.mk_and ctx exps1) ref_replaced_constraint in
                                let next_refinement_expr = Expr.substitute ref_constraint z3vars_ref next_step_vars in
                                debug(Printf.sprintf "Next refinement: %s\n" (Expr.to_string next_refinement_expr));
                                let vc2 = Boolean.mk_implies ctx (Boolean.mk_and ctx (ref_replaced_constraint :: exps3)) next_refinement_expr in
                                let vc = Boolean.mk_not ctx (Boolean.mk_and ctx [vc1; vc2]) in
                                z3_proof ctx env vc ref_replaced_constraint *)

                                (* Gets us phi[e1 / v] *)
                                let phi_e1 = Expr.substitute ref_constraint z3vars_ref e1_exps in
                                (* Gets us phi[e2 / v] *)
                                let phi_e2 = Expr.substitute ref_constraint z3vars_ref e2_exps in
                                debug(Printf.sprintf "phi_e1: %s\n" (Expr.to_string phi_e1));
                                debug(Printf.sprintf "phi_e2: %s\n" (Expr.to_string phi_e2));
                                (* vc1 === phi[x/v] => phi[e1 / v] *)
                                let vc1 = Boolean.mk_implies ctx ref_replaced_constraint phi_e1 in
                                (* vc2 === phi[x/v] => phi[e2 / v] *)
                                let vc2 = Boolean.mk_implies ctx ref_replaced_constraint phi_e2 in
                                (* Tries to disprove the VCs then adds them to the environment if no counterexample found *)
                                z3_proof ctx env (Boolean.mk_not ctx vc1) vc1;
                                z3_proof ctx env (Boolean.mk_not ctx vc2) vc2;
                            )
                    )
                )
                (* end goal: return an equality constraint btw original variables and their RHS, and also add the refinement constraint but with the variables substituted*)
          | _ -> debug (Printf.sprintf "else case");
              let body_exp = vc_gen_equation_expression ctx env e typenv p in
              debug (Printf.sprintf "body_exp: %s\n" (Expr.to_string body_exp));
              let pat_exp = 
               (match p.p_desc with 
               | Evarpat(n) -> debug (Printf.sprintf "Evarpat: %s\n" n.source); create_z3_var ctx env n.source
               | Etypeconstraintpat(p1,t) -> match t.desc with
                  | _ -> (let var_name = 
                  (match p1.p_desc with 
                     | Evarpat(n1) -> debug (Printf.sprintf "Etypeconstraintpat: %s\n" n1.source); add_constraint env (Boolean.mk_eq ctx body_exp (create_z3_var ctx env (n1.source))); n1.source
                     | _ -> debug (Printf.sprintf "Wrong pattern for variable in Etypeconstraintpat\n"); "undefined var_name") in
                     let (base_type_1, ref_var) = match t.desc with
                       | Erefinement(lbl, ref_exp) -> 
                         
                         add_variable_to_table ctx env typenv var_name ref_exp lbl;
                         let add_constraint_expr = (vc_gen_substitute (var_name) env ctx typenv) in
                         debug (Printf.sprintf "add_constraint exp: %s\n" (Expr.to_string add_constraint_expr));
                         z3_solve ctx env add_constraint_expr;
        
                         ((match (snd(lbl)).desc with
                             | Etypeconstr(long_name, _) -> (match long_name with
                               | Name(s) -> s
                               | Modname(q) -> q.id)
                             | _ -> "basetype_not_right"), fst(lbl))
                       | _ -> debug (Printf.sprintf "Wrong type expression for variable in Etypeconstraintpat\n"); ("undefined base_type", "undefined ref_var") in
                       create_z3_var_typed ctx env var_name base_type_1)
               | _ -> debug (Printf.sprintf "undefined_var"); create_z3_var ctx env "undefined_var") in
              debug (Printf.sprintf "pat_exp: %s\n" (Expr.to_string pat_exp));
              let ret_exp = Boolean.mk_eq ctx pat_exp body_exp in
              debug (Printf.sprintf "after ret_exp\n");
              debug (Printf.sprintf "EQ vc_gen_expression: %s\n" (Expr.to_string ret_exp));
              add_constraint env ret_exp
              (*ret_exp*)
            (* [p = e] *)
            (* | EQder(_, _, _, _) -> Printf.printf "EQder\n"
            (* [der n = e [init e0] [reset p1 -> e1 | ... | pn -> en]] *)
            | EQinit(_,_) -> Printf.printf "EQinit\n"
            (* [init n = e0 *)
            | EQnext(_,_,_) -> Printf.printf "EQnext\n"
            (* [next n = e] *)
            | EQpluseq(_,_) -> Printf.printf "EQpluseq\n"
            (* [n += e] *)
            | EQautomaton(_,_,_) -> Printf.printf "EQautomaton\n"
            (*added here
            | EQr_move of exp*)
            | EQpresent(_,_) -> Printf.printf "EQpresent\n"
            | EQmatch(_,_,_) -> Printf.printf "EQmatch\n"
            | EQreset(_,_) -> Printf.printf "EQreset\n"
            | EQemit(_,_) -> Printf.printf "EQemit\n"
            | EQblock(_) -> Printf.printf "EQblock\n"
            | EQand(_) -> Printf.printf "EQand\n" (* eq1 and ... and eqn *)
            | EQbefore(_) -> Printf.printf "EQbefore\n" (* eq1 before ... before eqn *)
            | EQforall(_) -> Printf.printf "EQforall\n" forall i in ... do ... initialize ... done *)
            | _ -> debug(Printf.sprintf "Ignoring vc_gen_equation for now\n"))
          | _ -> debug(Printf.sprintf "Ignoring this equation for now\n")
    

and create_validation_check ctx env elem1 elem2 = 
(*
    ctx -> z3 context
    constraints -> list of constraints to be satisfied by functions
    elem1 -> argument used as input in function call
    elem2 -> argument used during function definition

    return specified input contrained to funciton argument variable
*)
    debug (Printf.sprintf "\n --- CHECK INPUT VALIDITY ---\n");
    let input_binding = Boolean.mk_eq ctx (vc_gen_expression ctx env elem1 None) elem2 in
    (* Printf.printf "%s" (Expr.to_string input_binding); *)
    input_binding

and check_validity ctx env checks =
(*
    ctx -> z3 context
    constraints -> list of constraints to be satisfied by functions
    elem1 -> argument used as input in function call
    elem2 -> argument used during function definition

    check if elem1 satisfies the conditions imposed by elem2
*)
    debug (Printf.sprintf "\n --- CHECK INPUT VALIDITY ---\n");
    let arg_constraint = build_z3_premise ctx env in
    z3_solve ctx checks arg_constraint

and get_environment_constraints ctx local_env typenv arg =
(* 
  local_env -> environment 
  arg       -> vc_gen_expression argument used during funciton call

  Find constraints in the environment that are related to function input arguments
*)
  if (Hashtbl.mem local_env.var_env (Expr.to_string (vc_gen_expression ctx local_env arg typenv)) )
    then (
      Hashtbl.find local_env.var_env ( Expr.to_string (vc_gen_expression ctx local_env arg typenv))
    ) else (
      Boolean.mk_true ctx
    )

and prove_function ctx n local_env arg_list typenv =
(*  n        -> function name
    arg_list -> list containing vc_gen_expression arguments used during function call

    
    Use function space to determine if argument list has expected type
    from function space
*)
    (* if (Hashtbl.mem !stream_space n) then ()
    (* if it is a stream *)

    else ( *)(
      if (Hashtbl.mem !function_space n) 
        (* refinement function, make sure input list obeys constraints *)
        then (
          let ref_fun = Hashtbl.find !function_space n in
          debug (Printf.sprintf "TODO -- check if arguments obey constraints\n");
          print_function_temp n ref_fun;
          print_env local_env;
          (* let expr_test = vc_gen_expression ctx local_env (List.hd arg_list) None in
          Printf.printf "Arg_list[0]: %s\n" (Expr.to_string expr_test); *)
          let constraint_env = { exp_env = ref ref_fun.argument_constraints ; var_env = ref_fun.creation_env.var_env } in 
          let arguments = List.map (fun elem -> create_z3_var ctx constraint_env elem) ref_fun.argument_list in
          Printf.printf "map2 error is here!!\n";
          Printf.printf "name of function:%s\n" n;
          Printf.printf "length of ref_fun.argument_list:%d\n" (List.length ref_fun.argument_list);
          Printf.printf "# of Arguments in arg_list:%d arguments:%d\n" (List.length arg_list) (List.length arguments);
          let checks = List.map2 (fun elem1 elem2 -> create_validation_check ctx constraint_env elem1 elem2) arg_list arguments in
          (* let environment_constraints = List.map (get_environment_constraints ctx local_env typenv) arg_list in *)
          (* print_env ({ exp_env = ref( checks @ environment_constraints); var_env = Hashtbl.create 0}); *)
          let check_env = { exp_env = ref (checks @ !(local_env.exp_env)); var_env = Hashtbl.create 0} in
          check_validity ctx constraint_env check_env;
        ) 
        (* not a refinement function, so assume it is true*)
        else (
          debug (Printf.sprintf "Function %s not defined, assuming it is true\n" n);
          (* check if argument have other function calls*)
          ignore(List.iter (fun e_elem -> ignore(vc_gen_expression ctx local_env e_elem typenv)) arg_list);
        );
        (* dummy value since we don't need to handle non-refined vc_gen_expressions*)
        (* Figure out how to better ignore those vc_gen_expressions *)
      );
    Integer.mk_numeral_s ctx "42"


  (*let ref_fun = Hashtbl.find !function_space n in
  print_function_temp n ref_fun*)
  (* check argument against definition *)
  (* use z3 solve *) 

and prove_pair ctx env e_list tuple_type e typenv =
(*
    ctx      -> z3 context
    env      -> local scope environment
    e_list   -> list containing  tuple elements
    txp_list -> list containing tuple base types and binding variables  , i.e  x:int
    e        -> vc_gen_expression for tuple refinement type 
    typenv   -> local scope type environment

    Apply pair typing rule to tuple elements

    Gamma |- e1 : t1         Gamma |- e2 : [e1/x] t2
  ---------------------------------------------------- (DEPENDENT PAIR)
         Gamma |- (e1, e2) : Sigma(x : t1).t2

*)
  match e_list with
  (* | h :: t -> ( 
    (*
       h = 5
       t = (5 + 3, 5 + 4)

       (x = 5) && env

      x:int
    *)
    match (List.hd txp_list).desc with 
      | Erefinementpair(n, _ ) -> Printf.printf "Prove pair call - variable: %s\n" n; 
                                  e := Boolean.mk_and ctx [
                                          (Boolean.mk_eq ctx (create_z3_var ctx env n) (vc_gen_expression ctx env h typenv));
                                          !e ] ;
                                  Printf.printf "Success substitution: %s\n" (Expr.to_string !e);
                                  let txp_tl = List.tl txp_list in
                                   prove_pair ctx env t txp_tl e typenv
      | _ -> Printf.printf "Undefined type for pair element"
  ) *)
    | h :: [] -> ( 
      debug (Printf.sprintf "Last element\n");
            match (List.hd tuple_type).desc with 
              | Erefinementpair(n,typ) -> 
                (match typ.desc with 
                  | Etypeconstr(basetype, typ_exp_list) -> debug (Printf.sprintf "Etypeconstr pairs\n"); 
                                (
                                  match basetype with 
                                  | Name(btype) -> debug (Printf.sprintf "Basetype found %s\n" btype); debug(Printf.sprintf "Prove pair call - variable: %s\n" n);
                                        let last_element = Boolean.mk_eq ctx (create_z3_var ctx env n) 
                                        (vc_gen_expression ctx env h typenv) in
                                        z3_solve ctx (({exp_env = ref [last_element] ; var_env = Hashtbl.create 0})) !e
                                  | Modname(q) -> debug(Printf.sprintf "Modname found %s\n" q.id)
                                ) 
                  | _ -> debug(Printf.sprintf "Modname undefined pairs\n")
              )
              | Etypetuple(typ_list) -> debug(Printf.sprintf "Etypetupple:\n");
                            
                             let exp_list = (match h.e_desc with 
                              | Etuple (e_list) -> debug(Printf.sprintf "Etuple : \n"); 
                                    List.map (fun e -> e) e_list
                              | _ -> debug(Printf.sprintf "Not a tuple\n"); [h]
                            ) in
                            prove_pair ctx env exp_list typ_list e typenv

              | _ -> debug(Printf.sprintf "Undefined description type\n");
    )
    | h :: t -> ( 
        match (List.hd tuple_type).desc with 
                | Erefinementpair(n, typ) ->
                  (match typ.desc with
                  | Etypevar(basetype) -> (debug(Printf.sprintf "Prove pair call - variable: %s\n" n); 
                                           e := Expr.substitute_one !e (create_z3_var_typed ctx env n basetype)
                                                                       (vc_gen_expression ctx env h typenv);
                                                                  debug(Printf.sprintf "Success substitution\n"); 
                                           (* e := [
                                                   (Boolean.mk_eq ctx (create_z3_var ctx env n) (vc_gen_expression ctx env h typenv));
                                                   !e ] ; *)
                                           debug(Printf.sprintf "Success substitution: %s\n" (Expr.to_string !e));
                                           let txp_tl = List.tl tuple_type in
                                           prove_pair ctx env t txp_tl e typenv)
                  | Etypeconstr(basetype, typ_exp_list) -> debug(Printf.sprintf "Etypeconstr pairs\n"); 
                       (
                         match basetype with 
                         | Name(btype) -> debug(Printf.sprintf "Basetype found %s\n" btype); (debug(Printf.sprintf "Prove pair call - variable: %s\n" n);
                                           e := Boolean.mk_implies ctx 
                                                   (Boolean.mk_eq ctx (create_z3_var ctx env n) (vc_gen_expression ctx env h typenv))  (!e);
                                         (* e := Expr.substitute_one !e (create_z3_var ctx env n)
                                                                     (vc_gen_expression ctx env h typenv); *)
                                                               debug(Printf.sprintf "Success substitution: %s\n" (Expr.to_string !e));
                                                               let txp_tl = List.tl tuple_type in
                                                               prove_pair ctx env t txp_tl e typenv)
                         | Modname(q) -> debug(Printf.sprintf "Modname found %s\n" q.id)
                       ) 
                  | _ -> debug(Printf.sprintf "Undefined desc type\n")
                  )
                | _ -> debug(Printf.sprintf "Undefined modname\n")
    )
      


and vc_gen_operator ctx env typenv e e_list =
(*
        ctx    -> z3 context
        env    -> environment (list of z3 vc_gen_expressions)
        typenv -> typing environment ( Hash table of string = variable name * string = base type)
        e      -> vc_gen_expression vc_gen_operator
        e_list -> vc_gen_expression list, contains left and right arguments used by vc_gen_operator

                  e
              /       \
          e_list[1]  e_list[2]
        
        Builds z3 vc_gen_expression from vc_gen_operator and its left and right side

        Returns z3 vc_gen_expression
*)
  (*match desc with 
  (*TODO: check for list length*)

  match e_list with
    | op_l :: [] -> ()
      match e with 
        | "~" -> () (*Unary vc_gen_operator case*)
    | op_l :: op_r :: [] -> ()
      match e with 
        | _ -> () (*Binary vc_gen_operator case*)
    | _ -> () (*ERROR!*)
  *)
  debug(Printf.sprintf "Operator call %s : \n" e);
  Printf.printf "Operator call: %s\n" e;
  match e_list with 
  | op_l :: [] -> begin (* Unary operator case *)
    match e with
    | "box" -> debug(Printf.sprintf "box:\n");
      Quantifier.expr_of_quantifier (Quantifier.mk_forall ctx [] [] 
                                        (vc_gen_expression ctx env op_l typenv) None [] [] None None)
    | "diamond" -> debug(Printf.sprintf "diamond:\n");
        Quantifier.expr_of_quantifier (Quantifier.mk_exists ctx [] [] 
                                        (vc_gen_expression ctx env op_l typenv) None [] [] None None)
    | "~-" | "~-." -> debug(Printf.sprintf "Unary minus:"); Arithmetic.mk_unary_minus ctx (vc_gen_expression ctx env op_l typenv)
    | s -> debug(Printf.sprintf "Non-standard vc_gen_operator s : %s\n" s); 
      prove_function ctx s env e_list typenv
    | t -> debug(Printf.sprintf "Invalid vc_gen_expression symbol: %s\n" t); debug(Printf.sprintf "%d\n" (List.length e_list)); Integer.mk_numeral_s ctx "42"
  end
  | op_l :: op_r :: [] -> begin (* Binary operator case *)
    match e with 
    | ">=" -> Arithmetic.mk_ge ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv)
    | ">" -> Arithmetic.mk_gt ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv)
    | "<=" -> Arithmetic.mk_le ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv)
    | "<" -> Arithmetic.mk_lt ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv)
    | "=" -> Boolean.mk_eq ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv)
    | "!=" -> Boolean.mk_not ctx (Boolean.mk_eq ctx (vc_gen_expression ctx env op_l typenv) (vc_gen_expression ctx env op_r typenv))
    | "*." | "*" | "Stdlib.*." -> Arithmetic.mk_mul ctx [(vc_gen_expression ctx env op_l typenv); (vc_gen_expression ctx env op_r typenv)]
    | "+." | "+" | "Stdlib.+." -> Arithmetic.mk_add ctx [(vc_gen_expression ctx env op_l typenv); (vc_gen_expression ctx env op_r typenv)]
    | "-." | "-" | "Stdlib.-." -> Arithmetic.mk_sub ctx [(vc_gen_expression ctx env op_l typenv); (vc_gen_expression ctx env op_r typenv)]
    | "&&" -> Boolean.mk_and ctx [(vc_gen_expression ctx env op_l typenv); (vc_gen_expression ctx env op_r typenv)]
    | "||" -> Boolean.mk_or ctx [(vc_gen_expression ctx env op_l typenv); (vc_gen_expression ctx env op_r typenv)]
    | s -> debug(Printf.sprintf "Non-standard vc_gen_operator s : %s\n" (s)); prove_function ctx s env e_list typenv
    | t -> debug(Printf.sprintf "Invalid vc_gen_expression symbol: %s\n" t); debug(Printf.sprintf "%d\n" (List.length e_list)); Integer.mk_numeral_s ctx "42"
  end
  | _ -> raise (Z3FailedException "vc_gen_operator e_list matching error (having more than 2 arguments)")

(* translate vc_gen_expressions into Z3 constructs*)

and operator_vc_gen_expression_to_string ({ e_desc = desc; e_loc = loc}) =
(* Used to prevent creation of isolated vc_gen_expressions of operators: i.e >=, >, && *)
      match desc with 
      | Eglobal { lname = ln } -> debug(Printf.sprintf "Operator stringfy\n"); (match ln with
        (*TODO: Append a modname to Name if not found, rather than removing it from a Modname, so we preserve module info for global declarations *)
        | Name(n) -> debug(Printf.sprintf "Name: %s\n" n); n
        | Modname(qualid) -> debug(Printf.sprintf "Modname: %s\n" qualid.id); qualid.id) 
      | _ -> debug(Printf.sprintf "undefined behavior\n"); "undefined"

and vc_gen_operation ctx env typenv op e_list =
(*
    ctx -> z3 context
    env -> vc_gen_expression environment
    typenv -> typing environment
    op -> vc_gen_operation definition
    e_list -> list of operands

    Currently used to type check streams
*)
    match op, e_list with
    | Eunarypre, [e] -> debug(Printf.sprintf "Eunarypre\n"); Integer.mk_numeral_s ctx "42" 
    | Efby, [e1;e2] -> debug(Printf.sprintf "Efby\n"); Integer.mk_numeral_s ctx "42"
    | Eminusgreater, [e1;e2] -> debug(Printf.sprintf "Eminusgreater (->)\n"); Integer.mk_numeral_s ctx "42"
    (* e1 -> base case of stream*)
    (* e2 -> induction hypothesis of stream*)
    (* let new_stream = {initialization_var: e1; application_function: e2} in *)
    (* add_stream  *)
    | Eifthenelse, [e1; e2; e3] -> 
       (* let exp1 = (Expr.to_string (vc_gen_expression ctx env e1 typenv)) in
       let exp2 = (Expr.to_string (vc_gen_expression ctx env e2 typenv)) in
       let exp3 = (Expr.to_string (vc_gen_expression ctx env e3 typenv)) in
       debug(Printf.sprintf "if [%s] then [%s] else [%s]\n" exp1 exp2 exp3);  *)
       debug(Printf.sprintf "Eifthenelse\n");
       let expc = vc_gen_expression ctx env e1 typenv in
       let expt = vc_gen_expression ctx env e2 typenv in
       let expf = vc_gen_expression ctx env e3 typenv in
       Boolean.mk_ite ctx expc expt expf
    | Eup, [e] -> debug(Printf.sprintf "Eup\n"); Integer.mk_numeral_s ctx "42"
    | Einitial, [] -> debug(Printf.sprintf "Einitial\n"); Integer.mk_numeral_s ctx "42"
    | (Etest | Edisc | Ehorizon), [e] -> debug(Printf.sprintf "Etest | Edisc |Ehorizon\n"); Integer.mk_numeral_s ctx "42"
    | Eaccess, [e1; e2] -> debug(Printf.sprintf "Eaccess\n"); Integer.mk_numeral_s ctx "42"
    | Eupdate, [e1; i; e2] -> debug(Printf.sprintf "Eupdate\n"); Integer.mk_numeral_s ctx "42"
    | Eslice _, [e] -> debug(Printf.sprintf "Eslice\n"); Integer.mk_numeral_s ctx "42"
    | Econcat, [e1; e2] -> debug(Printf.sprintf "Econcat\n"); Integer.mk_numeral_s ctx "42"
    | Eatomic, [e] -> debug(Printf.sprintf "Eatomic\n"); Integer.mk_numeral_s ctx "42"
    | _ -> debug(Printf.sprintf "Operation undefined\n"); Integer.mk_numeral_s ctx "42"
    

(* the alpha substitution function*)
and vc_gen_substitute (var : string) env ctx typenv : expr = 
  (*
  var       ->   Variable to be substituted
  ctx       ->   Z3 context variable
  env       ->   Z3 local environment (reference of a list of Z3 vc_gen_expressions)
  typenv    ->   typing environment ( Hash table of string = variable name * custom_t = type)
  *)
  debug (Printf.sprintf "Calling vc_gen_substitute\n");
  match typenv with
  | Some(tbl) -> 
      debug (Printf.sprintf "typenv found\n");
      let sub_phi = (Hashtbl.find tbl var).phi in
      (* debug (Printf.sprintf "check 1\n"); *)
      let sub_reference_variable = (Hashtbl.find tbl var).reference_variable in
      debug(sub_reference_variable);
      let sub_basetype = (Hashtbl.find tbl var).base_type in
      debug(sub_basetype);
      let arg2 = (create_z3_var_typed ctx env sub_reference_variable sub_basetype) in
      let arg3 = (create_z3_var_typed ctx env var sub_basetype) in
      let arg1 = (vc_gen_expression ctx env sub_phi typenv) in
      (* Need to find out how vc_gen_expression creates arg1 (might help figure out the bug) *)
      debug(Printf.sprintf "Basetype in vc_gen_substitute:%s \n" sub_basetype);
      (* debug(Printf.sprintf "Arg1 EXP:%s \n" (sub_phi)); *)
      debug(Printf.sprintf "Arg1:%s \n" (Expr.to_string arg1));
      debug(Printf.sprintf "Arg2:%s \n" (Expr.to_string arg2));
      debug(Printf.sprintf "Arg3:%s \n" (Expr.to_string arg3));
      let after_subs = Expr.substitute_one arg1 arg2 arg3 in
      debug(Printf.sprintf "After sub:%s \n" (Expr.to_string after_subs));
      (* let a1 = Expr.mk_const ctx (Symbol.mk_string ctx "z") (Integer.mk_sort ctx) in
      let a2 = Expr.mk_const ctx (Symbol.mk_string ctx "z") (Integer.mk_sort ctx) in
      let a3 = Expr.mk_const ctx (Symbol.mk_string ctx "y") (Integer.mk_sort ctx) in
      debug(Printf.sprintf "A1:%s \n" (Expr.to_string a1));
      debug(Printf.sprintf "A2:%s \n" (Expr.to_string a2));
      debug(Printf.sprintf "A3:%s \n" (Expr.to_string a3));
      debug(Printf.sprintf "After sub test:%s \n" (Expr.to_string (Expr.substitute_one a1 (a2) (a3)))); *)
      after_subs
  | None -> debug (Printf.sprintf "Something is wrong with typenv\n"); Integer.mk_numeral_s ctx "42"

and vc_gen_expression ctx env ({ e_desc = desc; e_loc = loc }) typenv =
(*
        ctx    -> z3 context
        env    -> environment (list of z3 vc_gen_expressions)
        desc   -> vc_gen_expression desciption
        loc    -> vc_gen_expression location
        typenv -> typing environment ( Hash table of string = variable name * string = base type)

        Processes zelus vc_gen_expression into z3 vc_gen_expression

        Returns Z3 vc_gen_expression
*)
  match desc with
    (* | Econst(Evoid) -> Boolean.mk_true ctx *)
    | Econst(i) -> immediate ctx i
    | Eglobal { lname = ln } -> debug(Printf.sprintf "Eglobal vc_gen_expression\n"); create_z3_var ctx env (match ln with
      (*TODO: Append a modname to Name if not found, rather than removing it from a Modname, so we preserve module info for global declarations *)
      | Name(n) -> debug(Printf.sprintf "Name: %s\n" n); n
      | Modname(qualid) -> debug(Printf.sprintf "Modname: %s\n" qualid.id); qualid.id) 
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> 
      (* Printf.printf "vc_gen_expression %s\n" (Expr.to_string (vc_gen_expression ctx env e typenv)); *)
      (* debug(Printf.sprintf "vc_gen_expression app:\n"); *)
      Printf.printf "vc_gen_expression %s\n" (Expr.to_string (vc_gen_expression ctx env (List.hd e_list) typenv));


    (* TODO: print e_list *)    
      vc_gen_operator ctx env typenv (*Expr.to_string (vc_gen_expression ctx env e typenv)*) (operator_vc_gen_expression_to_string e) e_list 
    | Elocal(n) -> debug(Printf.sprintf "Elocal: %s : %d\n" n.source n.num);
          (match typenv with
          | Some(t) -> let ismember = (Hashtbl.mem t n.source) 
            in (if ismember then (let customtype = (Hashtbl.find t n.source) in
            debug(Printf.sprintf "%s has type %s" n.source customtype.base_type);
              (create_z3_var_typed ctx env n.source customtype.base_type))
          else
            (debug(Printf.sprintf "Creating var: %s\n" n.source); immediate ctx (Estring(n.source))) )
          | _ -> debug(Printf.sprintf "Error: typenv not given!\n"); Expr.mk_const ctx (Symbol.mk_string ctx n.source) (Real.mk_sort ctx))
    | Elet (l, e)-> 
        debug(Printf.sprintf "Elet parsing: \n");
        (* local ctx env typenv l;
         let local_exp = vc_gen_expression ctx env l typenv in
        Printf.printf (Expr.to_string local_exp);
        Printf.printf "Body:\n";*)
        debug(Printf.sprintf "Is recursive %b" l.l_rec);
        (List.iter (vc_gen_equation ctx env typenv) l.l_eq);
        let body_exp = vc_gen_expression ctx env e typenv in
        debug(Printf.sprintf "Body exp :%s \n" (Expr.to_string body_exp));
        print_env env;
        body_exp
        (* let eq_exp = vc_gen_equation ctx env typenv (List.hd l.l_eq) in *)
        (* Printf.printf "Body: %s\nEq: %s\n" (Expr.to_string body_exp) (Expr.to_string eq_exp); *)
        (* let res = Boolean.mk_eq ctx (body_exp) (eq_exp) in   *)
        (* let remainder = Boolean.mk_and ctx (List.map (fun a -> vc_gen_equation ctx env typenv a) (l.l_eq))in *)
        (* Printf.printf  "Body: %s\n" (Expr.to_string body_exp); *)
        (* Printf.printf "Remainder: %s\n" (Expr.to_string remainder); *)
        (* res *)

    | Econstr0 _ -> debug(Printf.sprintf "Econstr0\n"); Integer.mk_numeral_s ctx "42"
    | Econstr1 (_, _) -> debug(Printf.sprintf "Econstr1\n");Integer.mk_numeral_s ctx "42"
    | Elast _ -> debug(Printf.sprintf "Elast\n");Integer.mk_numeral_s ctx "42"
    | Eop ( op, e_list) -> debug(Printf.sprintf "Eop\n"); vc_gen_operation ctx env typenv op e_list
    (* used to type check pairs *)
    | Etuple (e_list) -> debug(Printf.sprintf "Etuple : \n"); 
    let exp_list_temp = List.map (fun e -> vc_gen_expression ctx env e typenv) e_list in
    let mk_tuple = Symbol.mk_string ctx "mk_tuple" in
    let field_name = [ Symbol.mk_string ctx "fst"; Symbol.mk_string ctx "snd"] in
    let field_sort = [ Integer.mk_sort ctx; Integer.mk_sort ctx] in
    let my_tuple = Tuple.mk_sort ctx mk_tuple field_name field_sort in
    debug(Printf.sprintf "My tuple: %s\n" (Sort.to_string my_tuple));
    let f = (Expr.mk_const ctx (Symbol.mk_string ctx "f") (Integer.mk_sort ctx))  in 
    let s = (Expr.mk_const ctx (Symbol.mk_string ctx "s") (Integer.mk_sort ctx)) in
    (* create tuple declaration and retrieve fields (fst, snd) *)
    let tuple_decl = Tuple.get_mk_decl my_tuple in
    let my_fields = Tuple.get_field_decls my_tuple in
    (* apply functions to get fst and snd elements*)
    let app1 = FuncDecl.apply (tuple_decl) [f; s] in
    let app2 = FuncDecl.apply (List.hd my_fields) [app1] in
    let app3 = FuncDecl.apply (List.hd (List.tl my_fields)) [app1] in
    (* equate functions to return vc_gen_expressions*)
    let exp1 = Boolean.mk_eq ctx app2 (List.hd exp_list_temp) in
    let exp2 = Boolean.mk_eq ctx app3 (List.hd (List.tl exp_list_temp)) in
    debug(Printf.sprintf "vc_gen_expression 1: %s\n" (Expr.to_string exp1));
    debug(Printf.sprintf "vc_gen_expression 2: %s\n" (Expr.to_string exp2));
    (* Printf.printf "Pair : [ "; *)
    (* List.iter (fun s -> Printf.printf "%s " (Expr.to_string s)) exp_list_temp; Printf.printf "]\n"; Integer.mk_numeral_s ctx "42" *)
    Integer.mk_numeral_s ctx "42"
    (* refinement tuples *)
    | Erefinementtuple(e_list, tuple_type, e) -> debug(Printf.sprintf "Erefinementtuple : \n");
     (*  5 , 5 + 3)
         [x:int; y:int]

         e = x < y && y < z
     *)
     (* Printf.printf "vc_gen_expression : %s\n" (Expr.to_string (vc_gen_expression ctx env e typenv)); *)
     (* List.iter ( fun elem -> Printf.printf "Element: %s\n"  (Expr.to_string (vc_gen_expression ctx env elem typenv))) e_list; *)
     let pair_constraint = vc_gen_expression ctx env e typenv in
     let type_tuple_list = (match tuple_type.desc with 
                             | Etypetuple(t_list) -> t_list                     
     ) in
     debug(Printf.sprintf "Pair constraint : %s\n" (Expr.to_string pair_constraint));
     prove_pair ctx env e_list type_tuple_list (ref pair_constraint) typenv;
     Integer.mk_numeral_s ctx "42"
    | Erecord_access (_, _) -> debug(Printf.sprintf "Erecord_acess\n");Integer.mk_numeral_s ctx "42"
    | Erecord _-> debug(Printf.sprintf "Erecord\n");Integer.mk_numeral_s ctx "42"
    | Erecord_with (_, _)-> debug(Printf.sprintf "Erecord_with\n");Integer.mk_numeral_s ctx "42"
    | Etypeconstraint (_, _)-> debug(Printf.sprintf "Etypeconstraint\n");Integer.mk_numeral_s ctx "42"
    | Epresent (_, _)-> debug(Printf.sprintf "Epresent\n");Integer.mk_numeral_s ctx "42"
    | Ematch (_, _, _)-> debug(Printf.sprintf "Ematch\n");Integer.mk_numeral_s ctx "42"
    | Eseq ( e1, e2)-> debug(Printf.sprintf ("Eseq : (e1 = %s e2 = %s)\n") (Expr.to_string (vc_gen_expression ctx env e1 typenv)) (Expr.to_string (vc_gen_expression ctx env e2 typenv)));
     Integer.mk_numeral_s ctx "42"
    | Eperiod _-> debug(Printf.sprintf "Eperiod\n"); Integer.mk_numeral_s ctx "42"
    | Eblock (_, _)-> debug(Printf.sprintf "Eblock\n"); Integer.mk_numeral_s ctx "42"  
    | _ -> (debug(Printf.sprintf "Ignore vc_gen_expression\n")); Integer.mk_numeral_s ctx "42"

    (*| Econstr0(lname) -> Zelus.Econstr0(longname lname)
    | Evar(Name(n)) ->
        begin try
            let { Rename.name = m } = Rename.find n env in Zelus.Elocal(m)
        with
          | Not_found -> Zaux.global (Lident.Name(n))
        end
    | Evar(lname) -> Zaux.global (longname lname)
    | Elast(n) -> Zelus.Elast(name loc env n)
    | Etuple(e_list) -> Zelus.Etuple(List.map (vc_gen_expression env ctx ) e_list)
    | Econstr1(lname, e_list) ->
        Zelus.Econstr1(longname lname, List.map (vc_gen_expression env ctx ) e_list)

    | Eop(op, e_list) ->
       Zelus.Eop(vc_gen_operator loc env op, List.map (vc_gen_expression env ctx) e_list)
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) ->
       Zelus.Eapp({ Zelus.app_inline = i; Zelus.app_statefull = r },
		  vc_gen_expression env ctx e, List.map (vc_gen_expression env ctx) e_list) 
  in emake loc desc
    
    | Erecord(label_e_list) ->
        Zelus.Erecord(recordrec loc env label_e_list)
    | Erecord_access(e1, lname) ->
        Zelus.Erecord_access(vc_gen_expression env ctx e1, longname lname)
    | Erecord_with(e, label_e_list) ->
       Zelus.Erecord_with(vc_gen_expression env ctx e, recordrec loc env label_e_list)
    | Etypeconstraint(e, ty) ->
        Zelus.Etypeconstraint(vc_gen_expression env ctx e, types env ty)
    | Elet(is_rec, eq_list, e_let) ->
        let env_p, env, eq_list = letin is_rec env eq_list in
        Zelus.Elet({ Zelus.l_rec = is_rec;
                     Zelus.l_eq = eq_list; 
                     Zelus.l_loc = loc; 
                     Zelus.l_env = Rename.typ_env env_p },
                    vc_gen_expression env ctx e_let)
    | Eseq(e1, e2) ->
        Zelus.Eseq(vc_gen_expression env ctx e1, vc_gen_expression env ctx e2)
    | Eperiod(p) ->
       Zelus.Eperiod(period env p)
    (*added here*)
    | Eassume(e) -> 
       Zelus.Eassume(vc_gen_expression env ctx e)   
    (*added here
    | Emove(e) ->
       Zelus.Emove(vc_gen_expression env e)	*)
    | Estore(c, k) ->
      		print_string("Robot command: "); print_string (c); print_string("\n");
      		print_string ("Value: "); print_float (k); print_string("\n"); Zelus.Estore(c, k)
    (* control structures are turned into equations *)
    | Ematch(e1, handlers) ->
        (* match e with P -> e1 => 
           local result do match e with P -> do result = e1 done in result *)
        let result = Zident.fresh "result" in
        let emit e = 
	  eqmake e.Zelus.e_loc (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let e1 = vc_gen_expression env ctx e1 in
        let handlers = 
	  match_handler_list 
	    (fun _ env e -> let e = vc_gen_expression env ctx e in block_with_emit emit e) 
	    Rename.empty env handlers in
	let eq = eqmake loc (Zelus.EQmatch(ref false, e1, handlers)) in
        Zelus.Eblock(block_with_result result [eq], var loc result)
   | Epresent(handlers, e_opt) ->
        (* Translate a present vc_gen_expression into a present vc_gen_equation *)
        (* [present sc1 -> e1 | ... else e] into *)
        (* [local res do present sc1 -> do res = e1 done *)
        (*               |... else do res = e in res]*)
        (* [present sc1 -> e1 | ... init e] into *)
        (* [local res do present sc1 -> do res = e1 done *)
        (*               | ...and init res = e in res]*)
        (* [present sc1 -> e1 ...] into *)
        (* [local res do present sc1 -> do emit res = e1 done] *)
        (* [emit e] returns either [emit x = e] or [x = e] according to *)
        (* the completeness of the definition. A signal is emitted when the *)
        (* present handler is not complete. *)
        let result = Zident.fresh "result" in
	let emit e =
	  match e_opt with 
	    | None -> 
	        eqmake e.Zelus.e_loc (Zelus.EQemit(result, Some(e)))
	    | Some(Init _)
	    | Some(Default _) ->
	        eqmake e.Zelus.e_loc
                  (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let handlers = 
	  present_handler_list
	    scondpat 
	    (fun _ env e -> let e = vc_gen_expression env ctx e in block_with_emit emit e)
	    Rename.empty env handlers in
	let b_opt, eq_init, is_mem = 
	    match e_opt with 
	      | None -> None, [], false
	      | Some(Init(e)) -> None, 
		[eqmake loc (Zelus.EQinit(result, vc_gen_expression env ctx e))],
		true
	      | Some(Default(e)) -> 
		 Some(block_with_emit emit (vc_gen_expression env ctx e)), [], false in
	let eq_list = 
	  eqmake loc (Zelus.EQpresent(handlers, b_opt)) :: eq_init in
	Zelus.Eblock(block_with_result result eq_list, var loc result)
    | Ereset(e_body, r) ->
  let e_body = vc_gen_expression env ctx e_body in
	let r = vc_gen_expression env ctx r in
	let result = Zident.fresh "result" in
	let eq = 
	  eqmake e_body.Zelus.e_loc
	    (Zelus.EQeq(varpat e_body.Zelus.e_loc result, e_body)) in
	let eq = eqmake loc (Zelus.EQreset([eq], r)) in
	Zelus.Eblock(block_with_result result [eq], var loc result)
    | Eautomaton(handlers, e_opt) ->
        let result = Zident.fresh "result" in
	let emit e = 
	  eqmake e.Zelus.e_loc (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let is_weak, handlers, e_opt = 
	  state_handler_list loc scondpat 
           (block locals
              (fun _ env e -> let e = vc_gen_expression env ctx e in [emit e]))
	   (block locals equation_list)
              vc_gen_expression 
	      Rename.empty env handlers ctx e_opt in
	let eq = eqmake loc (Zelus.EQautomaton(is_weak, handlers, e_opt)) in
	Zelus.Eblock(block_with_result result [eq], var loc result)
    | Eblock(b, e) ->
       let env, b = block_eq_list Rename.empty env b in
       let e = vc_gen_expression env ctx e in
       Zelus.Eblock(b, e) in
  emake loc desc*)
and get_return_type ctx env ({ e_desc = desc; e_loc = loc }) typenv =
(*
      ctx    ->  z3 context 
      env    ->  environment (list of z3 vc_gen_expressions)
      desc   ->  vc_gen_expression description
      loc    ->  vc_gen_expression location
      typenv ->  typing environment ( Hash table of string = variable name * string = base type)
      
      Converts the last vc_gen_expression defined within a function to a Z3 vc_gen_expression

      Returns functions last vc_gen_expression as Z3 vc_gen_expression
*)
    match desc with
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> 
      let return_var = vc_gen_expression ctx env (List.hd e_list) typenv in
      return_var 
    | Elet (l, e)-> 
        let body_exp = vc_gen_expression ctx env e typenv in
        body_exp
    | _ -> debug(Printf.sprintf "Not a function return type."); Integer.mk_numeral_s ctx "42"

and build_input_var ctx env e typenv istuple =
      if not istuple then (
        [(vc_gen_expression ctx env e typenv)]
      ) else (
        match e.e_desc with 
        | Etuple(e_list) ->
          [(vc_gen_expression ctx env (List.hd e_list) typenv) ; (vc_gen_expression ctx env (List.hd (List.tl e_list)) typenv) ]
      )

and build_return_var ctx env n istuple sort_enum =
      let return_type = sort2type sort_enum in
      if not istuple then (
      [create_z3_var_typed ctx env (Printf.sprintf "%s_return" n) return_type]
      ) else (
      [create_z3_var_typed ctx env (Printf.sprintf "%s_fst" n) return_type; create_z3_var_typed ctx env (Printf.sprintf "%s_snd" n) return_type]
      )

and build_next_step_var ctx env n sort_enum =
      let return_type = sort2type sort_enum in
      create_z3_var_typed ctx env (Printf.sprintf "%s_next" n) return_type

and get_expression_sort expr =
  (Sort.get_sort_kind (Expr.get_sort (expr)))

and qualident t =
(*
      t -> type data structure 

      Prints qualified identifier for given type
*)
    match t with
    | Lident.Name(n) -> debug(Printf.sprintf "%s \n" n)
    | Lident.Modname({ Lident.qual = m; Lident.id = s }) -> debug(Printf.sprintf "%s.%s \n" m s)

and print_type_element typ_elem =
    debug(Printf.sprintf "TYPE ELEMENT : \n");
    match typ_elem.desc with
    | Etypevar(n) -> debug(Printf.sprintf "Etypevar %s" n)
    | Etypeconstr(basetype, t_exp_list) -> debug(Printf.sprintf "Etypeconstr pairs\n"); 
                                      (
                                        match basetype with 
                                        | Name(btype) -> debug(Printf.sprintf "Basetype found %s\n" btype)
                                        | Modname(q) -> debug(Printf.sprintf "Modname found %s\n" q.id)
                                      ) 
    | Etypetuple(t_exp_list) -> debug(Printf.sprintf "Etypetuple\n"); List.iter (print_type_element) t_exp_list
    | Etypevec(t_exp, sz) -> debug(Printf.sprintf "Etypevec \n"); print_type_element t_exp
    | Etypefun(k, name, t_exp, t_exp2) -> debug(Printf.sprintf "TODO -- print ETYPEFUN")
    | Etypefunrefinement(k, name, typ_exp, typ_exp2, e) -> debug(Printf.sprintf "TODO -- print ETYPEFUNREFINEMENT")
    | Erefinementpairfuntype(t_exp_list, e) -> debug(Printf.sprintf "Erefinementpairfuntype\n"); List.iter (fun elem -> print_type_element elem; debug(Printf.sprintf "elem end\n\n")) t_exp_list
    | Erefinement((n, ty), e) -> debug(Printf.sprintf "Erefinement\n"); print_type_element ty
    | Erefinementpair(n, type_vc_gen_expression) -> debug(Printf.sprintf "Erefinementpair\n"); print_type_element type_vc_gen_expression

and add_tuple_list_to_type_env ctx env pat_list typ_exp typenv =
(*
      ctx      -> Z3 context
      txp_list -> list of tuple elements
      typ_exp  -> type vc_gen_expression information
      typ_env  -> typing environment

      Add each refined element of tuple to typing environment
*)
      List.iter (
        fun elem -> 
          (match elem.p_desc with
          | Evarpat(n) -> debug(Printf.sprintf "Evarpat in Etypeconstraintpat: (%s : %d) \n" n.source n.num);
            (*(vc_gen_pattern ctx env pat); *)
            (match typ_exp.desc with
            | Erefinement((n1, t), e) -> debug(Printf.sprintf "Adding to table: %s\n" n.source); 
              (
              match typenv with
              | Some(tbl) -> Hashtbl.add tbl n.source {base_type = (match t.desc with 
              (* Find and then add base type to local typing environment *)
              | Etypeconstr(l,_) -> (match l with
                  | Name(s) -> s
                  | Modname(q) -> q.id)
              | _ -> "Unspecified typenv match\n"); reference_variable = n.source; phi = e}
              | None -> ()
              )
            | Etypevar(n) -> debug(Printf.sprintf "Etypevar : %s\n" n)
            | Etypeconstr(t, typ_exp_list) -> debug(Printf.sprintf "Etypeconstr\n")
            | Etypetuple(typ_exp_list) ->  debug(Printf.sprintf "Etypetuple\n")
            | Etypevec(typ_exp, sz) -> debug(Printf.sprintf "Etypevec\n")
            | Etypefun(k, t, typ_exp1, typ_exp2) -> debug(Printf.sprintf "Etypefun\n")
            | Etypefunrefinement(k, t, typ_exp1, typ_exp2, e) -> debug(Printf.sprintf "Etypefunrefinement\n")
            | Erefinementpairfuntype(t_exp_list, e) -> debug(Printf.sprintf "Erefinementpairfuntype\n");
                     debug(Printf.sprintf "Element: %s\n" n.source);
                     let pair_vc_gen_expression = vc_gen_expression ctx env e typenv in
                     (add_constraint env pair_vc_gen_expression;
                     debug(Printf.sprintf "Adding vc_gen_expression: %s\n" (Expr.to_string pair_vc_gen_expression)))
            | Erefinementpair(n, t_exp) -> debug(Printf.sprintf "Erefinementpair\n")
            | _ -> debug(Printf.sprintf "Unspecified type constraint match\n"))
          | Econstpat(i) -> debug(Printf.sprintf "Econstpat\n")
          | Econstr0pat(t) -> debug(Printf.sprintf "Econstr0pat\n")
          | Econstr1pat(t, pat_list) -> debug(Printf.sprintf "Econstr1pat\n")
          | Etuplepat(pat_list) -> debug(Printf.sprintf "Etuplepat\n")
          | Ealiaspat(pat, t) -> debug(Printf.sprintf "Ealiaspat\n")
          | Eorpat(pat1, pat2) -> debug(Printf.sprintf "Eorpat\n")
          | Erecordpat(l_p_list) -> debug(Printf.sprintf "Erecordpat\n")
          | Etypeconstraintpat(pat, typ_exp) -> debug(Printf.sprintf "Etypeconstraintpat\n")
          | _ -> debug(Printf.sprintf "Unspecified pat.p_desc match\n"));   
          ) pat_list

and vc_gen_typ_exp_desc ctx env typenv t = 
(*
      ctx    -> z3 context
      env    -> environment (list of z3 vc_gen_expressions)
      typenv -> typing environment ( Hash table of string = variable name * string = base type)
      t      -> type vc_gen_expression 

      Creates z3 vc_gen_expression from type vc_gen_expression and adds it to the environment
*)
  match t.desc with
  | Etypevar(n) -> debug(Printf.sprintf "Etypevar %s\n" n)
  | Etypeconstr(t, txp_list) -> debug(Printf.sprintf "Etypeconstr\n"); qualident t; (List.iter (vc_gen_typ_exp_desc ctx env typenv) txp_list) 
  | Etypetuple(txp_list) -> debug(Printf.sprintf "Etypetuple\n"); (List.iter (vc_gen_typ_exp_desc ctx env typenv) txp_list)
  | Etypevec(texp , si) -> debug(Printf.sprintf "Etypevec\n")
  | Etypefun(k, t, texp, texp2) -> debug(Printf.sprintf "Etypefun\n")
  | Etypefunrefinement(k, t, te, te2, e) -> debug(Printf.sprintf "Etypefunrefinement\n")
  | Erefinement(t, e) -> debug(Printf.sprintf "Erefinement\n");  
       let expr = (vc_gen_expression ctx env e typenv) in
       (debug(Printf.sprintf "Returning from e local: %s\n" (Expr.to_string expr));
       (debug(Printf.sprintf "t.name %s" (fst t)));
       (* add_constraint env expr; *)
       z3_solve ctx env expr;
       )
  | Erefinementpairfuntype(txp_list, exp) -> debug(Printf.sprintf "Erefinementfunpair \n")
       (* List.iter (fun elem ->         ) txp_list *)

and vc_gen_pattern ctx env typenv pat = 
(*
      ctx    ->  z3 context     
      env    ->  environment (list of z3 vc_gen_expressions)
      typenv ->  typing environment ( Hash table of string = variable name * string = base type)
      pat    ->  vc_gen_pattern vc_gen_expression to be processed

      Processes the vc_gen_pattern vc_gen_expression and modifies the typing environment to account for new vc_gen_expressions
*)
  match pat.p_desc with
      | Ewildpat -> debug(Printf.sprintf "Ewildpat\n")
      | Econstpat(i) ->  debug(Printf.sprintf "Econstpat\n"); debug(Printf.sprintf "%s\n" (Expr.to_string (immediate ctx i)))
      | Econstr0pat(ln) -> debug(Printf.sprintf "Econstr0pat\n")
      | Econstr1pat(ln, p_list) -> debug(Printf.sprintf "Econstr1pat\n")
      | Etuplepat(p_list) -> debug(Printf.sprintf "Etplepat\n")
      | Ealiaspat(p, t) -> debug(Printf.sprintf "Ealiaspat\n")
      | Eorpat(p, p2) -> debug(Printf.sprintf "Eorpat\n")
      | Erecordpat(txp_list) -> debug(Printf.sprintf "Erecordpat\n")
      | Evarpat(n) ->
        debug(Printf.sprintf "Evarpat: (%s : %d) \n" n.source n.num)
      | Etypeconstraintpat(pat, typ_exp) -> debug(Printf.sprintf "Etypeconstraintpat: "); 
        (match pat.p_desc with
        | Evarpat(n) -> debug(Printf.sprintf "Evarpat in Etypeconstraintpat: (%s : %d) \n" n.source n.num);
          (*(vc_gen_pattern ctx env pat); *)
          (match typ_exp.desc with
          | Erefinement((n1,t), e) -> debug(Printf.sprintf "Adding to table: %s\n" n.source); 
            (
              match typenv with
                | Some(tbl) -> Hashtbl.add tbl n.source {base_type = (match t.desc with 
                (* Find and then add base type to local typing environment *)
                | Etypeconstr(l,_) -> (match l with
                    | Name(s) -> s
                    | Modname(q) -> q.id)
                | _ -> "Unspecified typenv match\n"); reference_variable = n.source; phi = e}
                | None -> ()
            )
          | Erefinementpairfuntype(t_exp_list, e) -> debug(Printf.sprintf "Erefinementpairfuntype\n")
          | Erefinementpair(n, t_exp) -> debug(Printf.sprintf "Erefinementpair\n")
          | Etypevar(n) -> debug(Printf.sprintf "Etypevar \n")
          | Etypeconstr(name, t_exp_list) -> debug(Printf.sprintf "Etypeconstr \n")
          | Etypetuple(t_exp_list) -> debug(Printf.sprintf "Etypetuple \n")
          | Etypevec(t_exp, sz) -> debug(Printf.sprintf "Etypevec \n")
          | Etypefun(k, n, t_exp, t_exp2) -> debug(Printf.sprintf "Etypefun \n")
          | Etypefunrefinement(k, n, t_exp, t_exp2, e) -> debug(Printf.sprintf "Etypefunrefinement \n")
          | _ -> debug(Printf.sprintf "Unspecified type constraint match\n"))
        | Etuplepat(pat_list) -> debug(Printf.sprintf "Etypetuple match: \n"); add_tuple_list_to_type_env ctx env pat_list typ_exp typenv
        | _ -> debug(Printf.sprintf "Unspecified pat.p_desc match\n"));   
        (vc_gen_typ_exp_desc ctx env (typenv) typ_exp)

let get_argument_list typenv =
(*
  typenv -> typing environment Hash table of string * string

  Iterates through hash tables and retrieves first element to the argument list

  Returns the argument list
*)
  let arg_list = ref [] in
  Hashtbl.iter (fun a b -> ( arg_list := (!arg_list) @ [a]; () )) typenv;
  !arg_list 

(* main entry functions *)
(* this function modifies the environemnt, returns unit *)

let implementation ff ctx env (impl (*: Zelus.implementation_desc Zelus.localized*))  =
(*
    ff        ->   printinf formart  (not used in this file)
    ctx       ->   Z3 context variable
    env       ->   Z3 local environment (reference of a list of Z3 vc_gen_expressions)
    impl      ->   a single element from the zelus AST list
    
    Applies a specified procedure to the element in the zelus AST list
*)
      match impl.desc with
      (* Add to Z3 an equality constraint that looks like: n == (Z3 parsed version of e) *)
      (* | Erefinementdecl(f, is_static, e) -> debug(Printf.sprintf "Econstdecl %s\n" f); 
        (* constraint : f = e *)
        add_constraint env (Boolean.mk_eq ctx (create_z3_var ctx env f) (vc_gen_expression ctx env e None));
        print_env env *)
      (* For constant functions, let x=f we assign x the type x:{float z | z=f} *)
      (* Refinement type of the form: let n1:n2{e1} = e2 *)
      | Econstdecl(n1, ty_refine, is_static, e2) ->
      	 debug(Printf.sprintf "Erefinementdecl %s\n" n1);
         add_constraint env (Boolean.mk_eq ctx (create_z3_var ctx env n1) (vc_gen_expression ctx env e2 None));
         (* z3_solve ctx env (vc_gen_expression ctx env e1 None); *)
         (* modified to be: calling z3_solve in vc_gen_typ_exp_desc 
          instead of in here *)
          (* add to Hash Table*)
          (* vc_gen_substitute *)
          let custom_type = erefinement2customt ty_refine ctx env None in
          add_type n1 custom_type;
          print_env env; 
          let expr_subs = vc_gen_substitute n1 env ctx (Some(!type_space)) in
          (* z3_solve *)
          z3_solve ctx env expr_subs;
         (* vc_gen_typ_exp_desc ctx env None ty_refine; *)
         print_env env

      | Erefinementfundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
		      f_body = e; f_loc = loc }) -> debug(Printf.sprintf "Efundecl %s\n" n); 
            debug(Printf.sprintf "# of Arguments: %d\n" (List.length p_list));

            (* let argc = (List.length p_list) in  *)
            let typenv = Hashtbl.copy !type_space in
            let local_env = { exp_env = ref []; var_env = Hashtbl.create 0}  in
            (List.iter (vc_gen_pattern ctx local_env (Some typenv)) p_list);
            Hashtbl.iter (fun a b -> debug(Printf.sprintf "%s:%s;" a b.base_type)) typenv;
            (* implementation_list ff ctx e; *) 
            (* debug(Printf.sprintf "Argc: %d\n" argc); *)
            
  
            (* treat function body as a program and prove conditions*)
            let expr = (vc_gen_expression ctx local_env e (Some typenv)) in
            add_constraint local_env expr;
            debug(Printf.sprintf "Function body vc_gen_expression handling: %s\n" (Expr.to_string expr));
            
            (* let f_new = { argument_constraints = [Boolean.mk_true ctx];
            variable_maps = Hashtbl.create 0;
            argument_list = ["a"];} in
            add_function n f_new; *)
            
            print_env local_env
            
            (* function proved, add to global environment, create a Z3 function 
            and a constraint defining its return type*)
            (* List.iter print_env_list !local_env; print_newline (); *)
             
      (* | Efundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
                      f_body = e; f_loc = loc; f_retrefine = rettype }) *)
      | Efundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
          f_body = e; f_loc = loc; f_retrefine = rettype }) -> debug(Printf.sprintf "Erefinementfundecl %s\n" n);
          
          (* added to test parsing *)
          (* TODO: remove the following line later and call substituition function *)
          let rettype = match rettype.desc with | Erefinement(_, exp)-> exp in
          
          (* let argc = (List.length p_list) in  *)
          let typenv = Hashtbl.copy !type_space in
          let local_env = { exp_env = ref []; var_env = Hashtbl.create 0} in
          let istuple = (match e.e_desc with
                          | Etuple(_) -> true
                          | _ -> false
                        ) in
          let isstream = (match e.e_desc with
                          | Elet(l, e) -> debug(Printf.sprintf "Stream elet\n"); (match (List.hd l.l_eq).eq_desc with 
                            | EQeq(p, e) -> ( match e.e_desc with
                                | Eop(op, e_list) -> debug(Printf.sprintf "Stream eop\n"); (
                                  match op, e_list with
                                  | Eminusgreater, [e1;e2] -> debug(Printf.sprintf "Stream eminusgreater\n"); true
                                  | _ -> debug(Printf.sprintf "Stream eminusgreater false\n"); false
                                  )  
                                | _ -> debug(Printf.sprintf "Stream eop false\n"); false   
                            )
                            | _ -> debug(Printf.sprintf "Stream eqeq false\n"); false 
                            )    
                          | _ -> debug(Printf.sprintf "Stream elet false\n"); false     
                          ) in
          if not isstream then (            
          (* add function input constraints to local environment *)
          (List.iter (vc_gen_pattern ctx local_env (Some typenv)) p_list);
          Hashtbl.iter (fun a b -> debug(Printf.sprintf "%s:%s;" a b.base_type)) typenv;
          (* implementation_list ff ctx e; *)


          (* Need to do:
           given function definition: let f (a:t_a{p_a}, b:t_b{p_b}...): t_f{p_f} = exp 
           Prove: (p_a & p_b & ...) -> exp:t_f{p_f}
           
           
           let b:int{b < -2} = -10 in 
           let f2 (x:int{x < 0}) : int:{f2_return >= 0} =
                let y = x*x in
                y
           in f2 b
             
            f b
            DISProve: ~((x<0) & (y=f2) -> (f2 >= 0))
            DISProve: ~(b < 0) (replace x with b)
            ( b = x ) -> (b < 0)

          *)
          (* let expr = (vc_gen_expression ctx env e (Some typenv)) in
          (add_constraint local_env expr;
          Printf.printf "Function body vc_gen_expression: %s\n" (Expr.to_string expr)); *)
          (* create function constraint to be proven *)
          let return_exp = (vc_gen_expression ctx local_env rettype (Some typenv)) in
          debug(Printf.sprintf "Return type vc_gen_expression: %s\n" (Expr.to_string return_exp));
          let function_argument_constraints = !(local_env.exp_env) in
          let function_variable_type_map = typenv in
          let function_argument_list = List.rev (get_argument_list( typenv )) in
          let f_new = { argument_constraints = function_argument_constraints;
                        variable_maps = function_variable_type_map;
                        argument_list = function_argument_list; 
                        creation_env = local_env; } in
          (* adding post and pre conditions of funtion to environment *)
          if (Expr.to_string return_exp)="true" 
            then Printf.printf "this is a true function\n"
            else (add_function n f_new);
          debug(Printf.sprintf "Printing function environment...\n");
          print_function_environment ();
          print_env local_env;

          (* treat function body as a program and prove conditions*)
          (* input_var is the last variable returned by the function *)
          (* let input_var = (vc_gen_expression ctx !local_env e (Some typenv)) in *)
          let input_var = build_input_var ctx local_env e (Some typenv) istuple in
          List.iter (fun input_elem -> debug(Printf.sprintf "Function body vc_gen_expression handling: %s\n" (Expr.to_string input_elem))) input_var;
          print_env local_env;
          
          
          (*let return_var = (get_return_type ctx local_env rettype (Some typenv)) in*)
          let return_var = build_return_var ctx local_env n istuple (Sort.get_sort_kind (Expr.get_sort (List.hd input_var))) in 
          List.iter (fun return_elem -> debug(Printf.sprintf "Return var: %s\n" (Expr.to_string return_elem))) return_var;
          (*let input_var = (get_return_type ctx local_env e (Some typenv)) in
          Printf.printf "Return var in: %s\n" (Expr.to_string input_var);*)
          (* let ret_constraint = (Boolean.mk_eq ctx return_var input_var) in *)
          let ret_constraint = List.map2 (fun input_elem return_elem -> Boolean.mk_eq ctx return_elem input_elem) input_var return_var in
          List.iter (fun ret_elem -> debug(Printf.sprintf "return definition: %s\n" (Expr.to_string ret_elem)); 
                     add_constraint local_env ret_elem) ret_constraint;
          (* add_constraint !local_env ret_constraint; *)
          print_env local_env;
          debug(Printf.sprintf "Prove constraint: %s\n" (Expr.to_string return_exp));
          
          debug(Printf.sprintf "Environment before solving: \n");
          print_env local_env;
          z3_solve ctx local_env return_exp;
          (* function proved, add to global environment, create a Z3 function 
          and a constraint defining its return type*)
          print_env local_env
          (* if proved rename return type with function name and add to global environment *)

          (* prove conditions *)

          (* implementation ff ctx local_env e; *)
          (* List.iter print_env_list !local_env; print_newline ()
           *)
          (* if properties are proved, then add to global environment*)

          (* TODO: make verif. conditions for function here *)

          (* TODO: define functions inside function*)
          ) else (
            (* Function is a stream *)
            (* add function input constraints to local environment *)
            debug(Printf.sprintf "--STREAM--\n");
            (List.iter (vc_gen_pattern ctx local_env (Some typenv)) p_list);
            Hashtbl.iter (fun a b -> debug(Printf.sprintf "%s:%s;" a b.base_type)) typenv;

            (* create function constraint to be proven *)
            let return_var = build_return_var ctx local_env n istuple (REAL_SORT) in 
            let return_exp = (vc_gen_expression ctx local_env rettype (Some typenv)) in
            debug(Printf.sprintf "Return type vc_gen_expression: %s\n" (Expr.to_string return_exp));
            let function_argument_constraints = !(local_env.exp_env) in
            let function_variable_type_map = typenv in
            let function_argument_list = List.rev (get_argument_list( typenv )) in
            let f_new = { argument_constraints = function_argument_constraints;
                          variable_maps = function_variable_type_map;
                          argument_list = function_argument_list; 
                          creation_env = local_env; } in
            add_function n f_new;
            debug(Printf.sprintf "Printing function environment...\n");
            print_function_environment ();
            print_env local_env;
            (* stream typing rule*)
            let base_exp = match e.e_desc with
                          | Elet(l, e) -> (match (List.hd l.l_eq).eq_desc with 
                            | EQeq(p, e) -> ( match e.e_desc with
                                | Eop(op, e_list) -> (
                                  match op, e_list with
                                  | Eminusgreater, [e1;e2] -> 
                                    (* prove stream base case *)
                                    let base_var = vc_gen_expression ctx local_env e1 (Some typenv) in
                                    let binding_exp = Boolean.mk_eq ctx base_var (List.hd return_var) in 
                                    let proof_env = {exp_env = ref (binding_exp ::!(local_env.exp_env));
                                                         var_env = (local_env.var_env)} in
                                    z3_solve ctx proof_env return_exp;
                                    (* prove stream induction hypothesis *)
                                    debug(Printf.sprintf "Processing e2\n");
                                    let fun_name = (match e2.e_desc with 
                                                    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> (operator_vc_gen_expression_to_string e)
                                    ) in
                                    debug(Printf.sprintf "Function name: %s \n" fun_name);
                                    let stream_application = Hashtbl.find !function_space fun_name in
                                    let stream_app_arg = List.hd stream_application.argument_list in
                                    let argument_relation_exp = Boolean.mk_eq ctx base_var ( create_z3_var ctx (stream_application.creation_env) stream_app_arg) in
                                    let fun_relation_exp = Boolean.mk_eq ctx (List.hd return_var) (create_z3_var ctx (stream_application.creation_env) (Printf.sprintf "%s_return" fun_name)) in
                                    let concatenate_envs = [argument_relation_exp; fun_relation_exp] @ !(stream_application.creation_env.exp_env) @ !(local_env.exp_env) in
                                    let function_proof_env = {exp_env = ref concatenate_envs; var_env = (local_env.var_env)} in
                                    debug(Printf.sprintf "Argument relation %s - Fun relation %s\n" (Expr.to_string argument_relation_exp) (Expr.to_string fun_relation_exp)); 
                                    z3_solve ctx function_proof_env return_exp; 
                                    let new_stream = {
                                      initialization_var=   base_var;
                                      application_function= fun_name;
                                      return_exp = return_exp;
                                      refinement_exp = !(local_env.exp_env) @ [binding_exp];
                                    } in add_stream n new_stream;
                                    true

                                    (* print_function fun_name stream_application; true *)
                                    (* let fun_exp = vc_gen_expression ctx !local_env e2 (Some typenv) in true *)


                                )  
                            )
                          )       
          
          in debug(Printf.sprintf "end\n")
          )
      | Eopen(n) -> debug(Printf.sprintf "Eopen %s\n" n)
      | Etypedecl(n, params, tydecl) -> debug(Printf.sprintf "Etypedecl %s\n" n)

(* let f x:tx y:ty z:tz = e:te *)
(* f has the type: tx -> ty -> tz -> te *)
(* to prove: assume x:tx y:ty z:tz, try to use this to prove e:te*)
(* in code, you will have something that looks like: *)
(* let f x:{float z| phi_x(z)} y:{float z| phi_y(z)} z:{float z' | phi_z(z')} = e:{float z | phi_e(z)} *)

(* Z3 constraints should look like: *)
(* (x,y,z are properly typed) -> (e is properly typed) *)
(* ([x/z]phi_x(z) & [y/z]phi_y(z) & [z/z']phi_z(z')) -> [e/z]phi_e(z) *)

(* the main entry function *)
let implementation_list ff (impl_list) (*: Zelus.implementation_desc Zelus.localized list ) : Zelus.implementation_desc Zelus.localized list*) = 
(*
    ff        ->   printinf formart  (not used in this file)
    ctx       ->   Z3 context variable
    impl_list ->   zelus program AST
    
    Creates a Z3 local environment and iterates through each argument of the AST list

    Returns the zelus program AST
*)
  print_string "Hello, this is Z3 Refinement\n";
  let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
  let z3env = {exp_env = ref []; var_env = Hashtbl.create 0} in
  List.iter (implementation ff ctx z3env) impl_list;
  if (!proof_error_count > 0) then (
  Printf.printf "\027[31m[WARNING]\027[0m Failed proof count : %d \n" !proof_error_count);
  impl_list

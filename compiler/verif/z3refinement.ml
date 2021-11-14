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

(*TODO :Change this to a Z3 expression type, then add stuff by AND-ing it on the head *)
(*let z3env = ref []*)

let add_constraint env premise = 
   env := premise :: (!env) 

(*
type z3env =
{
  scope: variable list;
  prev:  z3env;
}*)

(**
(*Define refinement type pattern*)
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
	
(* parse input expression into string and redirect to Z3 solver *)
let rec parse_expression e = 
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
       (*print_string (Printf.sprintf "Exp parsing: '%s' \n" (parse_expression e));
       print_string "Map start\n";
       let dummy = List.map (print_elt parse_expression) e_list in
       print_string "Eapp\n"; "1.0"*)
       let operator = Printf.sprintf "'%s'" (parse_expression e) in
       let exp_list = List.map parse_expression e_list in
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
	let arg = parse_expression e1 in
	let arg2 = parse_expression e2 in
	print_string arg; print_newline(); print_string arg2; print_newline();
	evaluate var ty (arg) (arg2)
*)
exception TestFailedException of string
let print_assignments m = 
  let decls = (Model.get_decls m) in
    List.iter (fun a -> (match (Model.get_const_interp m a) with
      | Some(e) -> Printf.printf "\t%s: %s\n" (Symbol.get_string (FuncDecl.get_name a)) 
          (if (Arithmetic.is_real e) then (Arithmetic.Real.to_decimal_string e 5) else (Expr.to_string e))
      | None -> ()
    )) decls

let build_z3_premise ctx l =
  match l with
  | [] -> Boolean.mk_true ctx
  | _ -> Boolean.mk_and ctx l

let z3_solve ctx env constraints = 
  let solver = (mk_solver ctx None) in
  let c = Boolean.mk_not ctx (Boolean.mk_implies ctx 
                                    (build_z3_premise ctx !env)
                                    (constraints)) in
  let s = (Solver.add solver [c]) in
  let q = check solver [] in
  (if q == SATISFIABLE then
    (Printf.printf "Counterexample found:\n";
    (let m = (get_model solver) in    
      		match m with 
          | None -> ()
		      | Some (m) -> 
	  	      (*Printf.printf "Model: \n%s\n" (Model.to_string m);*)
            print_assignments m;
      Printf.printf "Could not prove %s\n" (Expr.to_string constraints);
      raise (TestFailedException "")))
  else
    	    (Printf.printf "Passed\n"));
          add_constraint env constraints
  
	

let create_z3_var ctx s =
  Expr.mk_const ctx (Symbol.mk_string ctx s) (Real.mk_sort ctx)

let immediate ctx i = 
match i with
  | Ebool(b) ->  Boolean.mk_val ctx b 
  | Eint(i) -> (Printf.printf "Z3 Int %d\n") i; Integer.mk_numeral_s ctx (Printf.sprintf "%d" i)
  (*TODO: in general reals and floating points are not the same*)
  | Efloat(i) -> (Printf.printf "Z3 Float %f\n") i; Real.mk_numeral_s ctx (Printf.sprintf "%f" i)
  | Estring(c) -> Expr.mk_const ctx (Symbol.mk_string ctx c) (Real.mk_sort ctx)
  (*
  | Echar(c) -> Printf.sprintf "'%c'" c
  | Evoid -> Printf.sprintf ""
  *)
  | _ -> (Printf.printf "Ignore immediate \n"); Integer.mk_numeral_s ctx "42"

let rec operator ctx env e e_list =
  (*match desc with 
  (*TODO: check for list length*)

  match e_list with
    | op_l :: [] -> ()
      match e with 
        | "~" -> () (*Unary operator case*)
    | op_l :: op_r :: [] -> ()
      match e with 
        | _ -> () (*Binary operator case*)
    | _ -> () (*ERROR!*)
  *)
  match e with 
  | ">=" -> Arithmetic.mk_ge ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list))None)
  | ">" -> Arithmetic.mk_gt ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list)) None)
  | "<=" -> Arithmetic.mk_le ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list)) None)
  | "<" -> Arithmetic.mk_lt ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list)) None)
  | "==" -> Boolean.mk_eq ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list)) None)
  | "!=" -> Boolean.mk_not ctx (Boolean.mk_eq ctx (expression ctx env (hd e_list) None) (expression ctx env (hd (tl e_list))None ))
  | "*." | "Stdlib.*." -> Arithmetic.mk_mul ctx [(expression ctx env (hd e_list) None); (expression ctx env (hd (tl e_list)) None)]
  | s -> Printf.printf "Invalid expression symbol: %s" s; raise (Z3FailedException "Z3 verification failed")

(* translate expressions into Z3 constructs*)

and expression ctx env ({ e_desc = desc; e_loc = loc }) typenv =
  match desc with
    | Econst(i) -> immediate ctx i
    | Eglobal { lname = ln } -> create_z3_var ctx (match ln with
      (*TODO: Append a modname to Name if not found, rather than removing it from a Modname, so we preserve module info for global declarations *)
      | Name(n) -> n
      | Modname(qualid) -> qualid.id) 
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) -> 
      Printf.printf "Expression %s" (Expr.to_string (expression ctx env e None));
      operator ctx env (Expr.to_string (expression ctx env e None)) e_list
    | Elocal(n) -> Printf.printf "Elocal: %s : %d\n" n.source n.num;
          (match typenv with
          | Some(t) -> Printf.printf "%s has type %s" n.source (Hashtbl.find t n.source)
          | _ -> Printf.printf "Error: typenv not given!\n");
         Integer.mk_numeral_s ctx "42"
    | _ -> (Printf.printf "Ignore expression\n"); Integer.mk_numeral_s ctx "42"

    (*| Econstr0 _ -> Printf.printf "Econstr0\n";Integer.mk_numeral_s ctx "42"
    | Econstr1 (_, _) -> Printf.printf "Econstr1\n";Integer.mk_numeral_s ctx "42"
    | Elast _ -> Printf.printf "Elast\n";Integer.mk_numeral_s ctx "42"
    | Eop (_, _) -> Printf.printf "Eop\n";Integer.mk_numeral_s ctx "42"
    | Etuple _ -> Printf.printf "Etuple\n";Integer.mk_numeral_s ctx "42"
    | Erecord_access (_, _) -> Printf.printf "Erecord_acess\n";Integer.mk_numeral_s ctx "42"
    |Erecord _-> Printf.printf "Erecord\n";Integer.mk_numeral_s ctx "42"
    |Erecord_with (_, _)-> Printf.printf "Erecord_with\n";Integer.mk_numeral_s ctx "42"
    |Etypeconstraint (_, _)-> Printf.printf "Etypeconstraint\n";Integer.mk_numeral_s ctx "42"
    |Epresent (_, _)-> Printf.printf "Epresent\n";Integer.mk_numeral_s ctx "42"
    |Ematch (_, _, _)-> Printf.printf "Ematch\n";Integer.mk_numeral_s ctx "42"
    |Elet (_, _)-> Printf.printf "Elet\n"; Integer.mk_numeral_s ctx "42"
    |Eseq (_, _)-> Printf.printf "Eseq\n"; Integer.mk_numeral_s ctx "42"
    |Eperiod _-> Printf.printf "Eperiod\n"; Integer.mk_numeral_s ctx "42"
    |Eblock (_, _)-> Printf.printf "Eblock\n"; Integer.mk_numeral_s ctx "42"
    *)

    (*| Econstr0(lname) -> Zelus.Econstr0(longname lname)
    | Evar(Name(n)) ->
        begin try
            let { Rename.name = m } = Rename.find n env in Zelus.Elocal(m)
        with
          | Not_found -> Zaux.global (Lident.Name(n))
        end
    | Evar(lname) -> Zaux.global (longname lname)
    | Elast(n) -> Zelus.Elast(name loc env n)
    | Etuple(e_list) -> Zelus.Etuple(List.map (expression env ctx ) e_list)
    | Econstr1(lname, e_list) ->
        Zelus.Econstr1(longname lname, List.map (expression env ctx ) e_list)

    | Eop(op, e_list) ->
       Zelus.Eop(operator loc env op, List.map (expression env ctx) e_list)
    | Eapp({ app_inline = i; app_statefull = r }, e, e_list) ->
       Zelus.Eapp({ Zelus.app_inline = i; Zelus.app_statefull = r },
		  expression env ctx e, List.map (expression env ctx) e_list) 
  in emake loc desc
    
    | Erecord(label_e_list) ->
        Zelus.Erecord(recordrec loc env label_e_list)
    | Erecord_access(e1, lname) ->
        Zelus.Erecord_access(expression env ctx e1, longname lname)
    | Erecord_with(e, label_e_list) ->
       Zelus.Erecord_with(expression env ctx e, recordrec loc env label_e_list)
    | Etypeconstraint(e, ty) ->
        Zelus.Etypeconstraint(expression env ctx e, types env ty)
    | Elet(is_rec, eq_list, e_let) ->
        let env_p, env, eq_list = letin is_rec env eq_list in
        Zelus.Elet({ Zelus.l_rec = is_rec;
                     Zelus.l_eq = eq_list; 
                     Zelus.l_loc = loc; 
                     Zelus.l_env = Rename.typ_env env_p },
                    expression env ctx e_let)
    | Eseq(e1, e2) ->
        Zelus.Eseq(expression env ctx e1, expression env ctx e2)
    | Eperiod(p) ->
       Zelus.Eperiod(period env p)
    (*added here*)
    | Eassume(e) -> 
       Zelus.Eassume(expression env ctx e)   
    (*added here
    | Emove(e) ->
       Zelus.Emove(expression env e)	*)
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
	let e1 = expression env ctx e1 in
        let handlers = 
	  match_handler_list 
	    (fun _ env e -> let e = expression env ctx e in block_with_emit emit e) 
	    Rename.empty env handlers in
	let eq = eqmake loc (Zelus.EQmatch(ref false, e1, handlers)) in
        Zelus.Eblock(block_with_result result [eq], var loc result)
   | Epresent(handlers, e_opt) ->
        (* Translate a present expression into a present equation *)
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
	    (fun _ env e -> let e = expression env ctx e in block_with_emit emit e)
	    Rename.empty env handlers in
	let b_opt, eq_init, is_mem = 
	    match e_opt with 
	      | None -> None, [], false
	      | Some(Init(e)) -> None, 
		[eqmake loc (Zelus.EQinit(result, expression env ctx e))],
		true
	      | Some(Default(e)) -> 
		 Some(block_with_emit emit (expression env ctx e)), [], false in
	let eq_list = 
	  eqmake loc (Zelus.EQpresent(handlers, b_opt)) :: eq_init in
	Zelus.Eblock(block_with_result result eq_list, var loc result)
    | Ereset(e_body, r) ->
  let e_body = expression env ctx e_body in
	let r = expression env ctx r in
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
              (fun _ env e -> let e = expression env ctx e in [emit e]))
	   (block locals equation_list)
              expression 
	      Rename.empty env handlers ctx e_opt in
	let eq = eqmake loc (Zelus.EQautomaton(is_weak, handlers, e_opt)) in
	Zelus.Eblock(block_with_result result [eq], var loc result)
    | Eblock(b, e) ->
       let env, b = block_eq_list Rename.empty env b in
       let e = expression env ctx e in
       Zelus.Eblock(b, e) in
  emake loc desc*)

let qualident t =
    match t with
    | Lident.Name(n) -> Printf.printf "%s \n" n
    | Lident.Modname({ Lident.qual = m; Lident.id = s }) -> Printf.printf "%s.%s \n" m s

let print_env_list premise =
      (Printf.printf "Expression = %s ; " (Expr.to_string premise))

let rec type_exp_desc ctx env typenv t = match t.desc with
  | Etypevar(n) -> Printf.printf "Etypevar %s\n" n
  | Etypeconstr(t, txp_list) -> (Printf.printf "Etypeconstr\n"); qualident t; (List.iter (type_exp_desc ctx env typenv) txp_list) 
  | Etypetuple(txp_list) -> Printf.printf "Etypetuple\n"
  | Etypevec(texp , si) -> Printf.printf "Etypevec\n"
  | Etypefun(k, t, texp, texp2) -> Printf.printf "Etypefun\n" 
  | Etypefunrefinement(k, t, te, te2, e) -> Printf.printf "Etypefunrefinement\n"
  | Erefinement(t, e) -> Printf.printf "Erefinement\n";  
       let expr = (expression ctx env e typenv) in
       (add_constraint env expr;
       Printf.printf "%s\n" (Expr.to_string expr))

let rec pattern ctx env typenv pat = match pat.p_desc with
      | Ewildpat -> Printf.printf "Ewildpat\n"
      | Econstpat(i) -> Printf.printf "Econstpat\n"
      | Econstr0pat(ln) -> Printf.printf "Econstr0pat\n"
      | Econstr1pat(ln, p_list) -> Printf.printf "Econstr1pat\n"
      | Etuplepat(p_list) -> Printf.printf "Etplepat\n"
      | Ealiaspat(p, t) -> Printf.printf "Ealiaspat\n"
      | Eorpat(p, p2) -> Printf.printf "Eorpat\n"
      | Erecordpat(txp_list) -> Printf.printf "Erecordpat\n"
      | Evarpat(n) ->
        Printf.printf "Evarpat: (%s : %d) \n" n.source n.num;
      | Etypeconstraintpat(pat, typ_exp) -> (Printf.printf "Etypeconstraintpat: "); 
        (match pat.p_desc with
        | Evarpat(n) -> Printf.printf "Evarpat in Etypeconstraintpat: (%s : %d) \n" n.source n.num;
          (*(pattern ctx env pat); *)
          (match typ_exp.desc with
          | Erefinement(t, e) -> Printf.printf "Adding to table: %s\n" n.source; Hashtbl.add typenv n.source (match t.desc with 
            | Etypevar(n) -> n
            | Etypeconstr(l,_) -> (match l with
                | Name(s) -> s
                | Modname(q) -> q.id)
            | Etypetuple(_) -> "Etypetuple"
            | Etypevec(_,_) -> "Etypevec"
            | Etypefun(_,_,_,_) -> "Etypefun"
            | Etypefunrefinement(_,_,_,_,_) -> "Etypefunrefinement"
            | Erefinement(_,_) -> "Erefinement"
            | _ -> "unknown\n")
          | _ -> Printf.printf "unknown\n")
        | _ -> Printf.printf "unknown\n"); 
        Printf.printf "%s\n" (Hashtbl.find typenv "a");    
        (type_exp_desc ctx env (Some typenv) typ_exp)


(* main entry functions *)
(* this function modifies the environemnt, returns unit *)
let implementation ff ctx env (impl (*: Zelus.implementation_desc Zelus.localized*))  =
      match impl.desc with
      (* Add to Z3 an equality constraint that looks like: n == (Z3 parsed version of e) *)
      | Econstdecl(f, is_static, e) -> (Printf.printf "Econstdecl %s\n" f); 
        (*add_environment {name: n; type_t: ; refinement_t: true; assignment_t: expression Rename.empty e }*)
        add_constraint env (Boolean.mk_eq ctx (create_z3_var ctx f) (expression ctx env e None));
        List.iter print_env_list !env; print_newline ()
      (* For constant functions, let x=f we assign x the type x:{float z | z=f} *)
      (* Refinement type of the form: let n1:n2{e1} = e2 *)
      | Erefinementdecl(n1, n2, e1, e2) ->
      	 Printf.printf "Erefinementdecl %s %s\n" n1 n2;
         add_constraint env (Boolean.mk_eq ctx (create_z3_var ctx n1) (expression ctx env e2 None));
         z3_solve ctx env (expression ctx env e1 None);
         List.iter print_env_list !env; print_newline ()

      | Efundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
		      f_body = e; f_loc = loc }) -> (Printf.printf "Efundecl %s\n" n); 
            (Printf.printf "# of Arguments: %d\n" (List.length p_list)) 
      
      | Erefinementfundecl(n, { f_kind = k; f_atomic = is_atomic; f_args = p_list;
          f_body = e; f_loc = loc }, _) -> (Printf.printf "Erefinementfundecl %s\n" n); 
          let argc = (List.length p_list) in 
          let typenv = Hashtbl.create argc in
          (List.iter (pattern ctx env typenv) p_list);
          Hashtbl.iter (fun a b -> (Printf.printf "%s:%s;" a b)) typenv;
          List.iter print_env_list !env; print_newline ();
        (* create a local z3 environement to prove the funciton
           if fucntion is proven, add relation to global environment*)
        (*let z3localenv = ref [] in
        let x = (Expr.mk_const ctx (Symbol.mk_string ctx "x") (Real.mk_sort ctx)) in
        let y = (Expr.mk_const ctx (Symbol.mk_string ctx "y") (Real.mk_sort ctx)) in
        let fname = mk_string ctx "f" in
        let bs = Real.mk_sort ctx in
        let domain = [bs] in
        let f = FuncDecl.mk_func_decl ctx fname domain bs in
        let fapp = mk_app ctx f [x] in*)
      | Eopen(n) -> (Printf.printf "Eopen %s\n" n)
      | Etypedecl(n, params, tydecl) -> (Printf.printf "Etypedecl %s\n" n)

(* let f x:tx y:ty z:tz = e:te *)
(* f has the type: tx -> ty -> tz -> te *)
(* to prove: assume x:tx y:ty z:tz, try to use this to prove e:te*)
(* in code, you will have something that looks like: *)
(* let f x:{float z| phi_x(z)} y:{float z| phi_y(z)} z:{float z' | phi_z(z')} = e:{float z | phi_e(z)} *)

(* Z3 constraints should look like: *)
(* (x,y,z are properly typed) -> (e is properly typed) *)
(* ([x/z]phi_x(z) & [y/z]phi_y(z) & [z/z']phi_z(z')) -> [e/z]phi_e(z) *)

(* the main entry function *)
let implementation_list ff ctx (impl_list) (*: Zelus.implementation_desc Zelus.localized list ) : Zelus.implementation_desc Zelus.localized list*) = 
  print_string "Hello, this is Z3 Refinement\n";
  let z3env = ref [] in
  List.iter (implementation ff ctx z3env) impl_list;
  impl_list

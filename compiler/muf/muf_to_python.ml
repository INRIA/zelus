open Ast_helper
open Muf
open Format

let fv_expr expr = 
  Muf_utils.SSet.diff 
    (Muf_utils.fv_expr expr) 
    (Muf_utils.called_functions Muf_utils.SSet.empty expr)

let compile_fv : type a. formatter -> a expression -> unit = begin
  fun ff expr ->
    let fv = 
      Muf_utils.SSet.diff 
        (Muf_utils.fv_expr expr) 
        (Muf_utils.called_functions Muf_utils.SSet.empty expr)
    in
    let lv = Muf_utils.SSet.elements fv in
    fprintf ff "%a"
      (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") pp_print_string) lv
end

let rec compile_const : formatter -> constant -> unit = begin
  fun ff c ->
    begin match c with
    | Cbool x -> fprintf ff "%s" (String.capitalize_ascii (string_of_bool x))
    | Cint x -> fprintf ff "%d" x
    | Cint32 x -> fprintf ff "%ld" x
    | Cint64 x -> fprintf ff "%Ld" x
    | Cfloat x -> fprintf ff "%f" (float_of_string x)
    | Cstring x -> fprintf ff "%s" x
    | Cchar x -> fprintf ff "%c" x
    | Cunit -> fprintf ff "()"
    | Cany -> fprintf ff "None"
    end
end

let rec compile_patt : type a. formatter -> a pattern -> unit = begin
  fun ff p ->
    begin match p.patt with
    | Pid x -> fprintf ff "%s" x.name
    | Ptuple l -> 
      fprintf ff "(%a)" 
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_patt) l 
    | Pany -> fprintf ff "_"
    | Ptype _ -> ()
    | Pconst cst -> fprintf ff "%a" compile_const cst
    | Pconstr _ -> assert false
    end
end

let rec compile_expr :
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    let compile_app expr = 
      begin match expr with
      | Eapp(e1, e2) ->
        begin match e2.expr with
        | Etuple _ -> fprintf ff "%a%a" compile_expr e1 compile_expr e2
        | _ -> fprintf ff "%a(%a)" compile_expr e1 compile_expr e2
        end
      | _ -> assert false
      end
    in
    begin match e.expr with
    | Econst c -> fprintf ff "%a" compile_const c
    | Evar x -> fprintf ff "%s" (String.uncapitalize_ascii x.name)
    | Etuple l -> 
      fprintf ff "(%a)" 
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_expr) l
    | Erecord (l, oe) -> 
      let compile_field ff (x, e) = 
        fprintf ff "\"%s\": %a" x compile_expr e
      in
      begin match oe with
      | Some e -> 
        fprintf ff "{**%a, %a}" 
          compile_expr e 
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_field) l
      | None -> 
        fprintf ff "{%a}" 
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_field) l
      end
    | Efield (e, x) -> 
      fprintf ff "%a[\"%s\"]" compile_expr e x
    | Eapp ({ expr = Eapp ({ expr = Evar {name = op}}, e1) }, e2) (* Binary operator : e1 op e2 *)
      when op.[0] == '(' -> (* Infix operator *)
        let op_str = String.trim (String.sub op 1 ((String.index op ')')-1)) in (* Raises Not_found error if the closing parenthesis is missing *)
        let op_str =
          begin match op_str with
       (* | muF operator -> Python operator *)
          (* Integer arithmetic *)
          | "/" -> "//"
          (* Floating-point arithmetic *)
          | "+." -> "+" 
          | "-." -> "-"
          | "/." -> "/"
          | "*." -> "*"
          (* Comparisons *)
          | "=" -> "=="
          | "<>" -> "!="
          | "==" -> "is"
          | "!=" -> "is not"
          (* Bitwise operations *)
          | "asr" -> ">>"
          | "lsl" -> "<<"
          | "land" -> "&"
          | "lxor" -> "^"
          | "lor" -> "|"
          (* Boolean operations *)
          | "&" 
          | "&&" -> "and"
          | "||" -> "or"
          (* String operations *)
          | "^" -> "+"
          (* List operations *)
          | "@" -> "+"
          (* Not rewritten operators *)
          | "+"
          | "-"
          | "*" 
          | ">"
          | ">="
          | "<"
          | "<="
          | "**" -> op_str
          (* Unknown operator, e.g. might be a name surrounded by unnecessary parentheses *)
          | _ -> ""
          end
        in
        if op_str = "" then 
          compile_app e.expr 
        else
          fprintf ff "(%a %s %a)" compile_expr e1 op_str compile_expr e2
    | Eapp ({ expr = Evar {name = op}}, e1) (* Unary operator : op e1*)
      when op.[0] == '(' -> 
      let op_str = String.trim (String.sub op 1 ((String.index op ')')-1)) in (* Raises Not_found error if the closing parenthesis is missing  *)
        let op_str =
          begin match op_str with
          | "~-" -> "-"
          | "~-." -> "-"
          | "-." -> "-"
          | "lnot" -> "~"
          | "not" -> op_str
          | _ -> ""
          end
        in
        if op_str = "" then 
          compile_app e.expr 
        else 
          fprintf ff "(%s %a)"op_str compile_expr e1
    | Eapp (e1, e2) -> compile_app e.expr
    | Eif (e, { expr=Eapp({expr=Evar{name=n1}}, args1) },
              { expr=Eapp({expr=Evar{name=n2}}, args2) }) 
      when args1 = args2 ->
      fprintf ff "cond(@,    @[<v 0>%a,@,%s,@,%s,@,%a)@]" 
        compile_expr e 
        n1 
        n2
        compile_expr args1
    | Eif _ -> Format.eprintf "Eif incompatible with the Python-JAX backend\n" ; assert false
    | Esequence (e1, e2) ->
      fprintf ff "@[<v 0>%a@,%a@]" compile_expr e1 compile_expr e2
    | Esample (prob, e) ->
      fprintf ff "sample(%s, %a)" prob compile_expr e
    | Eobserve (prob, e1, e2) ->
      fprintf ff "observe(%s, %a, %a)" prob compile_expr e1 compile_expr e2
    | Efactor (prob, e) ->
      fprintf ff "factor(%s, %a)" prob compile_expr e
    | Einfer (e,id) -> fprintf ff "init (infer(%a)(%s))" compile_expr e id.name
    | Ecall_init (e) -> 
        fprintf ff "init (%a)" compile_expr e
    | Ecall_reset(e) -> 
        fprintf ff "reset (%a)" compile_expr e
    | Ecall_step (e1, e2) -> 
        fprintf ff "step (%a, %a)" compile_expr e1 compile_expr e2
    | Efun _
    | Elet _
    | Ematch _ 
    | Econstr _ -> assert false
    end
end

and compile_return :
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with 
    | Elet ({ patt = Pid {name=f_name} }, 
            { expr = Efun (p_args, e1) }, 
            e2) -> 
      fprintf ff "@[<v 4>def %s(%a):@,%a@]@," 
        f_name
        compile_patt p_args
        compile_return e1;
      fprintf ff "@[<v 0>%a@]"
        compile_return e2
    | Elet (p, e1, e2) -> 
      fprintf ff "@[<v 0>%a = %a@,%a@]" 
          compile_patt p 
          compile_expr e1
          compile_return e2
    | Esequence (e1, e2) -> 
      fprintf ff "@[<v 0>%a@,%a@]" compile_expr e1 compile_return e2
    | Erecord(l, oe) ->
      fprintf ff "return %a" compile_expr {e with expr = Erecord(l, oe)}
    | _ -> fprintf ff "return %a" compile_expr e
    end
end


let compile_node : 
  type a b. formatter -> identifier -> a pattern list -> (a pattern, b expression) node -> unit = begin
  fun ff f params n ->
    let compile_method m ff (p, e) =
      fprintf ff "@[<v 4>def %s(self, *args):@,%a = args@,%a@]@," 
            m
            compile_patt p 
            compile_return e
    in
    let compile_class ff (f, n) = 
      fprintf ff "@register_pytree_node_class@,@[<v 4>class %s(Node):@,%a@,%a@]"
        f.name 
        (compile_method "init") ({patt=Ptuple([]); pmeta = ();}, n. n_init) 
        (compile_method "step") n.n_step
    in
    begin match params with
    | [] -> compile_class ff (f, n)
    | _ -> begin
        List.iter 
          (fun p -> fprintf ff "@[<v 4>def %s(%a):@," f.name compile_patt p )
          params;
        fprintf ff "%a@,return %s" compile_class (f, n) f.name;
        List.iter (fun _ -> fprintf ff "@]") params
      end
    end
end

let compile_decl : type a. formatter -> a declaration -> unit = begin
  fun ff d ->
    begin match d.decl with
    | Ddecl (p, e) ->
        fprintf ff "%a = %a@," 
            compile_patt p 
            compile_expr e
    | Dfun (f, p, e) ->
        fprintf ff "@[<v 4>def %s(*args):@,%a = args@,%a@]" 
          f.name 
          compile_patt p 
          compile_return e
    | Dnode (f, p, n) -> compile_node ff f p n
    | Dtype _ -> ()
    | Dopen m -> fprintf ff "import %s" (String.uncapitalize_ascii m)
    end
end


let compile_program : formatter -> unit program -> unit = begin
  fun ff p ->
    let p =
      List.map
        (fun d ->
          { decl = map_decl_desc (fun p -> p) Muf_rewrites.remove_match d.decl })
        p
    in
    let p = Muf_flatten.compile_program p in
    fprintf ff "@[<v 0>";
    fprintf ff  "from muflib import Node, step, reset, init@,";
    fprintf ff  "from jax.lax import cond@,";
    fprintf ff  "from jax.tree_util import register_pytree_node_class@,@,";
    List.iter (compile_decl ff) p;
    fprintf ff "@,@]@."
end

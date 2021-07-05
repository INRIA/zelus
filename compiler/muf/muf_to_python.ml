open Ast_helper
open Muf
open Format

type op = 
  Infix of string
| Prefix of string
| Unary of string
| Fun_call

let fresh_nat = 
  let i = ref (-1) in 
  fun _ -> begin
    incr i ; !i
  end

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

let to_py_op s =
  begin match s with 
  | "&" 
  | "&&" ->  "logical_and"
  | "or"
  | "||" ->  "logical_or"
  | "not" -> "logical_not"
  | _ ->
    let to_py_op_char c =
      begin match c with
      (* Non-alphanumeric symbols accepted in OCaml but not in Python *)
      | '$' -> 'd'
      | '&' -> 'a'
      | '*' -> 's'
      | '+' -> 'p'
      | '-' -> 'm'
      | '/' -> 'q'
      | '=' -> 'e'
      | '>' -> 'u'
      | '@' -> 't'
      | '^' -> 'h'
      | '|' -> 'v'
      | '~' -> 'l'
      | '!' -> 'x'
      | '?' -> 'g'
      | '%' -> 'c'
      | '<' -> 'i'
      | ':' -> 'b'
      | '.' -> 'o'
      | _ -> c
      end
    in "_" ^ (String.map to_py_op_char s)
  end

let rec compile_const : formatter -> constant -> unit = begin
  fun ff c ->
    begin match c with
    | Cbool x -> fprintf ff "%s" (String.capitalize_ascii (string_of_bool x))
    | Cint x -> fprintf ff "%d" x
    | Cint32 x -> fprintf ff "%ld" x
    | Cint64 x -> fprintf ff "%Ld" x
    | Cfloat x -> fprintf ff "%f" (float_of_string x)
    | Cstring x -> fprintf ff "\"%s\"" x
    | Cchar x -> fprintf ff "'%c'" x
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
    let compile_args ff e =
      begin match e.expr with
      | Etuple _ -> fprintf ff "%a" compile_expr e
      | _ -> fprintf ff "(%a)"compile_expr e
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
    | Eapp ({ expr = Evar {name = op}}, e1) (* Unary and infix operators *)
      when op.[0] == '(' || op = "not" -> 
        let op = if op.[0] == '('
          (* String.index raises Not_found error if the closing parenthesis is missing *)
          then String.trim (String.sub op 1 ((String.index op ')')-1)) 
          else op 
        in
        let op = to_py_op op in
        fprintf ff "%a" compile_expr { e with expr = Eapp ({e with expr = Evar {name = op}}, e1) }
    | Eapp (e1, e2) -> fprintf ff "%a%a" compile_expr e1 compile_args e2
    | Eif (e, { expr=Eapp({expr=Evar{name=n1}}, args1) },
              { expr=Eapp({expr=Evar{name=n2}}, args2) }) 
      when args1 = args2 ->
      fprintf ff "cond(@,    @[<v 0>%a,@,%s,@,%s,@,%a)@]" 
        compile_expr e 
        n1 
        n2
        compile_expr args1
    | Eif (e, et, ef) ->
      fprintf ff "cond(@,    @[<v 0>%a,@,lambda _: %a,@,lambda _: %a,@,None)@]" 
        compile_expr e
        compile_expr et
        compile_expr ef
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
    | Econstr ({name=n}, opt_e) -> 
      let args ff a = 
        begin match a with 
        | None -> ()
        | Some e -> fprintf ff "%a" compile_args e
        end
      in
      fprintf ff "%s%a" n args opt_e
    | Efun _
    | Elet _
    | Ematch _ -> assert false
    end
end

and compile_return :
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with 
    | Elet ({ patt = Pid {name=f_name} }, 
            { expr = Efun (p_args, e1) }, 
            e2) -> 
      fprintf ff "@[<v 4>def %s(%a):@,%a@]@,%a" 
        f_name
        compile_patt p_args
        compile_return e1
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

let compile_constructors :
string -> formatter -> (identifier * type_expression list option) list -> unit = begin
  fun type_name ff l_constructors -> 
    let compile_one ff ({name=constructor_name}, opt) =
      begin match opt with 
      | None -> fprintf ff "%s = %s(%d)" constructor_name type_name (fresh_nat ())
      | Some l -> assert false (* TODO *)
      end
    in 
    fprintf ff "%a" 
        (pp_print_list compile_one) l_constructors
  end

let compile_type_class :
formatter -> string -> unit = begin
  fun ff type_name ->
    fprintf ff "@register_pytree_node_dataclass@,@[<v 4>class %s(J_dataclass):@,pass@]" type_name
  end

let compile_type :
  formatter -> (identifier * string list * type_declaration) -> unit = begin
  fun ff ({name=n}, l, t) ->
    begin match t with
    | TKvariant_type l -> fprintf ff "%a@,%a" compile_type_class n (compile_constructors n) l
    | TKabbrev _
    | TKrecord _ 
    | TKabstract_type -> assert false (* TODO *)
    end
  end

let to_py_module s = String.uncapitalize_ascii s

let compile_decl : type a. formatter -> a declaration -> unit = begin
  fun ff d ->
    begin match d.decl with
    | Ddecl (p, {expr = Elet(p_let, e1, e2)}) ->
      let f_name = Muf_rename.freshname "_f_decl" in
      fprintf ff "@[<v 4>def %s():@,%a = %a@,%a@]@,%a = %s()@," 
        f_name
        compile_patt p_let
        compile_expr e1
        compile_return e2 
        compile_patt p
        f_name
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
    | Dtype l -> 
      fprintf ff "%a" 
        (pp_print_list compile_type) l 
    | Dopen m -> 
      let m = to_py_module m in
        begin match Muf_libs_name.SSet.find_opt m Muf_libs_name.module_names_zeluc with
          | Some _ -> fprintf ff "from zlax.%s import *@," m
          | None ->
            begin match Muf_libs_name.SSet.find_opt m Muf_libs_name.module_names_probzeluc with
            | Some _ -> fprintf ff "from probzelus.%s import *@," m
            | None -> fprintf ff "from %s import *@," m
            end
          end
        end
end

let compile_import_modules : type t. formatter -> Muf_utils.SSet.t -> unit = begin
  fun ff s ->
    let f m = 
      let m = to_py_module m in
        begin match Muf_libs_name.SSet.find_opt m Muf_libs_name.module_names_zeluc with
        | Some _ -> fprintf ff "from zlax import %s@," m
        | None -> 
          begin match Muf_libs_name.SSet.find_opt m Muf_libs_name.module_names_probzeluc with
          | Some _ -> fprintf ff "from probzelus import %s@," m
          | None -> fprintf ff "import %s@," m
          end
        end
    in
    Muf_utils.SSet.iter f s
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
    let to_import = Muf_utils.imported_modules p in
    fprintf ff "@[<v 0>";
    fprintf ff "from zlax.std import *@,@,";
    compile_import_modules ff to_import;
    List.iter (compile_decl ff) p;
    fprintf ff "@,@]@."
end

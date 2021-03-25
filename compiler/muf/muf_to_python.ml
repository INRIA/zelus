open Ast_helper
open Muf
open Format

let freshname = 
  let i = ref 0 in 
  fun prefix -> begin
    incr i;
    prefix ^ "_" ^ (string_of_int !i)
  end

let is_flat e =
  let rec flat_expr acc e =
    let acc =
      begin match e.expr with
      | Elet _ -> false
      | _ -> acc
      end
    in
    fold_expr_desc (fun acc _ -> acc) flat_expr acc e.expr
  in 
  flat_expr true e

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

let rec compile_const: formatter -> constant -> unit = begin
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
    | Cany -> fprintf ff "()"
    end
end

let rec compile_patt: type a. formatter -> a pattern -> unit = begin
  fun ff p ->
    begin match p.patt with
    | Pid x -> fprintf ff "%s" x.name
    | Ptuple l -> 
      fprintf ff "(%a)" 
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_patt) l 
    | Pany -> fprintf ff "_"
    | Ptype _ -> ()
    end
end

let rec compile_expr:
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with
    | Econst c -> fprintf ff "%a" compile_const c
    | Evar x -> fprintf ff "%s" (String.uncapitalize_ascii x.name)
    | Etuple l -> 
      let l = List.map (fun x -> compile_flatten ff x) l in
      fprintf ff "(%a)" 
        (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_expr) l
    | Erecord (l, oe) -> 
      let l = List.map (fun (x, e) -> (x, compile_flatten ff e)) l in
      let compile_field ff (x, e) = 
        fprintf ff "\"%s\": %a" x compile_expr e
      in
      begin match oe with
      | Some e -> 
        let e = compile_flatten ff e in 
        fprintf ff "{**%a, %a}" 
          compile_expr e 
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_field) l
      | None -> 
        fprintf ff "{%a}" 
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_field) l
      end
    | Efield (e, x) -> 
      let e = compile_flatten ff e in
      fprintf ff "%a[\"%s\"]" compile_expr e x
    | Eapp (e1, e2) ->
      let e1 = compile_flatten ff e1 in
      let e2 = compile_flatten ff e2 in 
      begin match e1.expr with
      | Evar {name=op} when op.[0] == '(' -> (* Infix operator *)
          begin match e2.expr with (* Arguments of the operator as a tuple. Support only for binary operators (arguments as a tuple of size 2) *)
          | Etuple [e1; e2] -> 
            let op_str = (String.sub op 1 ((String.index op ')')-1)) in (* Raises Not_found if bad parentheses *)
              let op_str = 
                begin match String.trim op_str with
                | "+." -> "+" (* Ocaml float operator -> Python operator*)
                | "-." -> "-"
                | "/." -> "/"
                | "*." -> "*"
                | other -> other
                end
              in
              fprintf ff "%a %s %a" compile_expr e1 op_str compile_expr e2
          | _ -> eprintf "Tuple of size 2 expected for the infix binary operator." ; assert false
          end
      | _ -> begin match e2.expr with
             | Etuple _ -> fprintf ff "%a%a" compile_expr e1 compile_expr e2
             | _ -> fprintf ff "%a(%a)" compile_expr e1 compile_expr e2
             end
      end
    | Eif (e, e1, e2) ->
        let e = compile_flatten ff e in
        let e1 = compile_flatten ff e1 in 
        let e2 = compile_flatten ff e2 in
        fprintf ff "%a if %a else %a" 
          compile_expr e1 
          compile_expr e 
          compile_expr e2
    | Elet (p, e1, e2) ->
      let e1 = compile_flatten ff e1 in
      let e2 = compile_flatten ff e2 in
      fprintf ff "@[<v 0>%a = %a@,%a@]" 
        compile_patt p 
        compile_expr e1
        compile_expr e2
    | Esequence (e1, e2) ->
      fprintf ff "@[<v 0>%a@,%a@]" compile_expr e1 compile_expr e2
    | Esample (prob, e) ->
      let e = compile_flatten ff e in
      fprintf ff "sample(%s, %a)" prob compile_expr e
    | Eobserve (prob, e1, e2) ->
      let e1 = compile_flatten ff e1 in
      let e2 = compile_flatten ff e2 in
      fprintf ff "observe(%s, %a, %a)" prob compile_expr e1 compile_expr e2
    | Efactor (prob, e) ->
      let e = compile_flatten ff e in
      fprintf ff "factor(%s, %a)" prob compile_expr e
    | Einfer ((p, e), args) -> fprintf ff "infer_step(TODO)"
    | Einfer_init (e,id) -> fprintf ff "infer_init(%a, %s)" compile_expr e id.name
    | Einfer_reset (e1,id,e2) -> fprintf ff "infer_reset(TODO)"
    | Einfer_step (e1,id,e2) -> fprintf ff "infer_step(TODO)"
    end
end

and compile_flatten:
  type a. formatter -> a expression -> a expression = begin
    fun ff e ->
      begin match is_flat e with
      | true -> e
      | false -> 
        let f = freshname "_f" in
        let r = freshname "_r" in
        fprintf ff "@[<v 4>def %s(%a):@,%a@]@,%s = %s(%a)@,"
          f
          compile_fv e
          compile_return e
          r
          f
          compile_fv e;
        {e with expr = Evar({name = r})}
      end
  end

and compile_return:
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with 
    | Elet (p, e1, e2) -> 
      let e1 = compile_flatten ff e1 in
      fprintf ff "@[<v 0>%a = %a@,%a@]" 
          compile_patt p 
          compile_expr e1
          compile_return e2
    | Esequence (e1, e2) -> 
      fprintf ff "@[<v 0>%a@,%a@]" compile_expr e1 compile_return e2
    | Erecord(l, oe) ->
      let l = List.map (fun (x, e) -> (x, compile_flatten ff e)) l in
      fprintf ff "return %a" compile_expr {e with expr = Erecord(l, oe)}
    | _ -> fprintf ff "return %a" compile_expr e
    end
end

let compile_decl : type a. formatter -> a declaration -> unit = begin
  fun ff d ->
    begin match d.decl with
    | Ddecl (p, e) ->
        let e = compile_flatten ff e in
        fprintf ff "%a = %a@," 
            compile_patt p 
            compile_expr e
    | Dfun (f, p, e) ->
        fprintf ff "@[<v 4>def %s(*args):@,%a = args@,%a@]@.@." 
          f.name 
          compile_patt p 
          compile_return e
    | Dtype (t, params, k) -> ()
    | Dopen m -> fprintf ff "import %s@." (String.uncapitalize_ascii m)
    end
end


let compile_program : type a. formatter -> a program -> unit = begin
  fun ff p ->
    List.iter (compile_decl ff) p;
    fprintf ff "@."
end

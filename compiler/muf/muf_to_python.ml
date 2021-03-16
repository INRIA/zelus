open Ast_helper
open Muf
open Format

let freshname prefix = 
  let i = ref 0 in 
  fun () -> begin
    incr i;
    "_" ^ prefix ^ "_" ^ (string_of_int !i)
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
    | Cany -> fprintf ff "_"
    end
end

let rec compile_patt: type a. formatter -> a pattern -> unit = begin
  fun ff p ->
    begin match p.patt with
    | Pid x -> fprintf ff "%s" x.name
    | Ptuple l -> fprintf ff "(%a)" (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_patt) l 
    | Pany -> fprintf ff "_"
    end
end

let rec compile_expr:
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with
    | Econst c -> fprintf ff "%a" compile_const c
    | Evar x -> fprintf ff "%s" x.name
    | Etuple l -> fprintf ff "(%a)" (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_expr) l
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
        fprintf ff "{%a}" (pp_print_list ~pp_sep:(fun ff () -> fprintf ff ", ") compile_field) l
      end
    | Efield (e, x) -> fprintf ff "%a[\"%s\"]" compile_expr e x
    | Eapp (e1, e2) -> fprintf ff "%a(%a)" compile_expr e1 compile_expr e2
    | Eif (e, e1, e2) ->
        fprintf ff "%a if %a else %a" 
          compile_expr e1 
          compile_expr e 
          compile_expr e2
    | Elet (p, e1, e2) ->
        let n = freshname "f" () in 
        fprintf ff "@[<v 0>@[<v 4>def %s():@,%a@]@,%a = %s()@,%a@]" n compile_return e1 compile_patt p n compile_expr e2
        (* fprintf ff "@[<v 0>%a = %a@,%a@]" compile_patt p compile_expr e1 compile_expr e2 *)
    | Esequence (e1, e2) ->
        fprintf ff "%a;%a" compile_expr e1 compile_expr e2
    | Esample (prob, e) ->
        fprintf ff "sample(%a)" compile_expr e
    | Eobserve (prob, e1, e2) ->
        fprintf ff "observe(%a, %a)" compile_expr e1 compile_expr e2
    | Efactor (prob, e) ->
        fprintf ff "factor(%a)" compile_expr e
    | Einfer ((p, e), args) ->
        fprintf ff "infer_step(TODO)"
        (* let infer_id = Longident.Lident "infer_step" in
        Exp.apply (Exp.ident (with_loc infer_id))
          [ (Nolabel, Exp.fun_ Nolabel None (compile_patt p) (compile_expr e));
            (Nolabel, compile_expr args) ] *)
    end
end

and compile_return:
  type a. formatter -> a expression -> unit = begin
  fun ff e -> 
    begin match e.expr with
    | Elet (p, e1, e2) ->
      let n = freshname "f" () in 
      fprintf ff "@[<v 0>@[<v 4>def %s():@,%a@]@,%a = %s()@,%a@]" n compile_return e1 compile_patt p n  compile_return e2
    | Esequence (e1, e2) ->
      fprintf ff "%a;%a" compile_expr e1 compile_return e2
    | _ -> fprintf ff "return %a" compile_expr e
    end
  end

let compile_decl : type a. formatter -> a declaration -> unit = begin
  fun ff d ->
    match d.decl with
    | Ddecl (p, e) ->
        let n = freshname "f" () in 
        fprintf ff "@[<v 0>@[<v 4>def %s():@,%a@]@,%a = %s()@]@.@." n compile_return e compile_patt p n
    | Dfun (f, p, e) ->
        let pn = freshname "p" () in
        fprintf ff "@[<v 4>def %s(%s):@,%a=%s@,%a@]@.@." f.name pn compile_patt p pn compile_return e
    | Dtype (t, params, k) -> ()
    | Dopen m ->
        fprintf ff "open %s@." m
end


let compile_program : type a. formatter -> a program -> unit = begin
  fun ff p ->
    List.iter (compile_decl ff) p;
    fprintf ff "@."
end
open Ast_helper
open Muf

let with_loc: type a. a -> a with_loc = begin
  fun x ->
    { txt = x;
      loc = Location.none; }
end

let rec compile_const: constant -> Parsetree.expression = begin
  fun c ->
    begin match c with
    | Cbool x ->
        let b =
          with_loc (Longident.Lident (string_of_bool x))
        in
        Exp.construct b None
    | Cint x -> Exp.constant (Const.int x)
    | Cint32 x -> Exp.constant (Const.int32 x)
    | Cint64 x -> Exp.constant (Const.int64 x)
    | Cfloat x -> Exp.constant (Const.float x)
    | Cstring x -> Exp.constant (Const.string x)
    | Cchar x -> Exp.constant (Const.char x)
    | Cunit -> Exp.construct (with_loc (Longident.Lident "()")) None
    | Cany ->
        Exp.apply
          (Exp.ident
             (with_loc (Longident.Ldot (Longident.Lident "Obj", "magic"))))
          [Nolabel, compile_const Cunit]
    end
end

let rec compile_patt: type a. a pattern -> Parsetree.pattern = begin
  fun p ->
    begin match p.patt with
    | Pid x -> Pat.var (with_loc x.name)
    | Ptuple l -> Pat.tuple (List.map compile_patt l)
    | Pany -> Pat.any ()
    | Ptype (p, _) -> compile_patt p
    end
end

let rec compile_expr:
  type a. a expression -> Parsetree.expression = begin
  fun e ->
    begin match e.expr with
    | Econst c -> compile_const c
    | Evar x -> Exp.ident (with_loc (Longident.Lident x.name))
    | Etuple l -> Exp.tuple (List.map compile_expr l)
    | Erecord (l, oe) ->
        let compile_field (x, e) =
          (with_loc (Longident.Lident x), compile_expr e)
        in
        Exp.record (List.map compile_field l) (Option.map compile_expr oe)
    | Efield (e, x) ->
        Exp.field (compile_expr e) (with_loc (Longident.Lident x))
    | Eapp (e1, e2) -> 
      (
      match e1.expr with
      | Evar v when v.name.[0] == '(' -> (* Infix operator *)
          match e2.expr with 
          | Etuple [op1;op2] as l -> (* Arguments of the operator as a tuple. Support only for binary operators (arguments as a tuple of size 2) *)
              Exp.apply (Exp.apply (compile_expr e1) [Nolabel, compile_expr op1]) [Nolabel, compile_expr op2]
          | _ -> Format.eprintf "Tuple of size 2 expected for the infix binary operator." ; assert false
      | _ -> Exp.apply (compile_expr e1) [Nolabel, compile_expr e2]
      )
    | Eif (e, e1, e2) ->
        Exp.ifthenelse (compile_expr e)
          (compile_expr e1) (Some (compile_expr e2))
    | Elet (p, e1, e2) ->
        Exp.let_ Nonrecursive
          [ { Parsetree.pvb_pat = compile_patt p;
   	      pvb_expr = compile_expr e1;
   	      pvb_attributes = [];
   	      pvb_loc = Location.none; } ]
          (compile_expr e2)
    | Esequence (e1, e2) ->
        Exp.sequence (compile_expr e1) (compile_expr e2)
    | Esample (prob, e) ->
        let sample = Exp.ident (with_loc (Longident.Lident "sample'")) in
        Exp.apply sample
          [Nolabel, Exp.tuple [ Exp.ident (with_loc (Longident.Lident prob));
                                compile_expr e] ]
    | Eobserve (prob, e1, e2) ->
        let observe = Exp.ident (with_loc (Longident.Lident "observe'")) in
        Exp.apply observe
          [ (Nolabel, Exp.tuple [ Exp.ident (with_loc (Longident.Lident prob));
                                  Exp.tuple [ compile_expr e1; compile_expr e2 ]
                                ]) ]
    | Efactor (prob, e) ->
        let factor = Exp.ident (with_loc (Longident.Lident "factor'")) in
        Exp.apply factor
          [Nolabel, Exp.tuple [ Exp.ident (with_loc (Longident.Lident prob));
                                compile_expr e ]]
    | Einfer ((p, e), args) ->
        let infer_id = Longident.Lident "infer_step" in
        Exp.apply (Exp.ident (with_loc infer_id))
          [ (Nolabel, Exp.fun_ Nolabel None (compile_patt p) (compile_expr e));
            (Nolabel, compile_expr args) ]
    | Einfer_init (n, f_init) ->
        let infer_id = Longident.Lident "infer_init" in
        Exp.apply (Exp.ident (with_loc infer_id))
          [ (Nolabel, (compile_expr n));
            (Nolabel, (Exp.ident (with_loc (Longident.Lident f_init.name)))) ]
    | Einfer_reset (n, f_step, args) ->
        let infer_id = Longident.Lident "infer_reset" in
        Exp.apply (Exp.ident (with_loc infer_id))
          [ (Nolabel, compile_expr n);
            (Nolabel, (Exp.ident (with_loc (Longident.Lident f_step.name))));
            (Nolabel, compile_expr args) ]
    | Einfer_step (n, f_step, args) ->
        let infer_id = Longident.Lident "infer_step" in
        Exp.apply (Exp.ident (with_loc infer_id))
          [ (Nolabel, compile_expr n);
            (Nolabel, (Exp.ident (with_loc (Longident.Lident f_step.name))));
            (Nolabel, compile_expr args) ]
    end
end

let rec compile_core_type : core_type -> Parsetree.core_type = begin
  fun t ->
    match t with
    | Tany -> Typ.any ()
    | Tvar x -> Typ.var x
    | Ttuple l -> Typ.tuple (List.map compile_core_type l)
    | T_constr (x, l) ->
        Typ.constr (with_loc (Longident.Lident x))
          (List.map compile_core_type l)
end

let compile_type_kind : type_kind -> Parsetree.type_kind = begin
  fun k ->
    match k with
    | TKrecord l ->
        Ptype_record
          (List.map (fun (x, t) ->
               Type.field (with_loc x) (compile_core_type t))
              l)
end

let compile_decl : type a. a declaration -> Parsetree.structure_item = begin
  fun d ->
    match d.decl with
    | Ddecl (p, e) ->
        Str.value Nonrecursive [ Vb.mk (compile_patt p) (compile_expr e) ]
    | Dfun (f, p, e) ->
        Str.value Nonrecursive
          [ Vb.mk (Pat.var (with_loc f.name))
              (Exp.fun_ Nolabel None (compile_patt p) (compile_expr e)) ]
    | Dtype (t, params, k) ->
        Str.type_ Recursive
          [ Type.mk
              ~params:(List.map (fun a -> (Typ.var a,
                                           (Asttypes.NoVariance,
                                            Asttypes.NoInjectivity)))
                         params)
              ~kind:(compile_type_kind k)
             (with_loc t.name) ]
    | Dopen m ->
        Str.open_ (Opn.mk (Mod.ident (with_loc (Longident.Lident m))))
end


let compile_program : type a. a program -> Parsetree.structure = begin
  fun p ->
    List.map compile_decl p
end

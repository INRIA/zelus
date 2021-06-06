(* global data in the symbol tables *)
open Misc
open Ident

    
type 'a info = { qualid : Lident.qualident; info : 'a }

(* values in the symbol table *)
type value_desc =
    { mutable value_typ: Deftypes.typ_scheme; (* its type scheme *)
      mutable value_caus: Defcaus.tc_scheme option; (* its causality scheme *)
      mutable value_init: Definit.ti_scheme option; (* its init. scheme *)
    }

(* Value constructors *)
type constr_desc = { constr_arg: Deftypes.typ list;
                     constr_res: Deftypes.typ;
                     constr_arity: int }

and label_desc =
    { label_arg: Deftypes.typ; (* if x:arg then x.m: res *)
      label_res: Deftypes.typ; }

type type_desc =
  { mutable type_desc: type_components;
    mutable type_parameters: int list;
  }

and type_components =
    | Abstract_type
    | Variant_type of constr_desc info list
    | Record_type of label_desc info list
    | Abbrev of Deftypes.typ list * Deftypes.typ 
        (* type ('a1,...,'an) t = ty *)

let value_desc is_static typs qualident = 
  { value_typ = typs; value_caus = None;
    value_init = None }
let set_type { info = ({ value_typ = _ } as v) } tys = 
  v.value_typ <- tys
let set_causality { info = ({ value_caus = _ } as v) } tys = 
  v.value_caus <- Some(tys)
let set_init { info = ({ value_init = _ } as v) } tys = 
  v.value_init <- Some(tys)

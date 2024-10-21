(* All functions above are purely functional. Because some compiler passes *)
(* (e.g., type systems) update the global environment, we also provide *)
(* an imperative interface. This should change in future versions *)
module Imperative =
struct
  let c_empty = { name = "";
                  values = (E.empty: no_info E.t);
                  types = (E.empty: no_info E.t); 
                  constr = (E.empty: no_info E.t);
                  label = (E.empty: no_info E.t) }
                
  let empty = { current = c_empty; opened = []; modules = E.empty }

  let current = c_empty
      
  let modules = empty
      
  let clear () =
    current.values <- E.empty; current.types <- E.empty;
    current.constr <- E.empty; current.label <- E.empty
               
  let write oc = output_value oc current

  let find_value qualname = find_value qualname modules
  let find_type qualname = find_type qualname modules
  let find_constr qualname = find_constr qualname modules
  let find_label qualname = find_label qualname modules

  let find_module modname =
    let v, genv = find_module modname modules in
    modules.modules <- genv.modules;
    v
      
  let open_module modname =
    let m = find_module modname in
    modules.opened <- m :: modules.opened
                             
  let initialize modname =
    current.name <- modname;
    List.iter open_module !default_used_modules
      
  let add_value f v = 
    if E.mem f current.values then raise (Already_defined f);
    current.values <- E.add f v current.values
        
  let add_type f typ_desc =
    if E.mem f current.types then raise (Already_defined f);
    current.types <- E.add f typ_desc current.types
  let add_constr f ty_res =
    if E.mem f current.constr then raise (Already_defined f);
    current.constr <- E.add f ty_res current.constr
  let add_label f label_desc =
    if E.mem f current.label then raise (Already_defined f);
    current.label <- E.add f label_desc current.label
end
(* exception we make, to reuse the (old style) previous implementation *)
(* of Zelus *)

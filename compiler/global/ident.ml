(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* naming and local environment *)

type t =
  { num : int;        (* a unique index *)
    source : string;  (* the original name in the source *)
  }

and element_t =
  { arrnm : string;   (* global array name *)
    index : t;        (* index into the array*)
  }

type t_alias = t

let compare id1 id2 = compare id1.num id2.num

let name id = id.source ^ "_" ^ (string_of_int id.num)

let source id = id.source

let num = ref 0
let fresh s = num := !num + 1; { num = !num; source = s }

let fprint_t ff id = Format.fprintf ff "%s" (name id)

module M = struct
  type t = t_alias
  let compare = compare
  let fprint = fprint_t
end

module Env =
struct
  include (Map.Make(M))

  let singleton i tentry = add i tentry empty

  let fprint_t fprint_v ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "@[%a: %a@]" M.fprint k fprint_v v) s;
    Format.fprintf ff "}@]"

  (* debugging printer for (Ident.t * Ident.t * Ident.t) Ident.Env.t *)
  let fprint_3ident ff s =
    let fprint_v ff (id1, id2, id3) =
      Format.fprintf ff "@[%a@]"
        (Pp_tools.print_list_r M.fprint "("","")") [id1; id2; id3] in
    fprint_t fprint_v ff s

  (* let append env0 env = fold add env0 env *)
  let append env0 env =
    fold (fun x v acc -> update x (function _ -> Some(v)) acc)
      env0 env
end

module S = struct
  include (Set.Make(M))
  let fprint_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a@ " M.fprint e) s;
    Format.fprintf ff "}@]"

  let fresh s ss =
    let add_fresh id m = Env.add id (fresh s) m in
    fold add_fresh ss Env.empty

  let domain acc env =
    Env.fold (fun k _ set -> add k set) env acc

  let range acc env =
    Env.fold (fun _ v set -> add v set) env acc

  let map f s = fold (fun e rs -> add (f e) rs) s empty
end


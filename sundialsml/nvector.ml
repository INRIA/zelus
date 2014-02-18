(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*            Timothy Bourke (INRIA) and Marc Pouzet (LIENS)           *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

type 'a nvector

module Mutable = struct
  type 'a nvector_ops = {
    nvclone           : 'a -> 'a;
    nvdestroy         : ('a -> unit) option;
    nvspace           : ('a -> (int * int)) option;
    nvlinearsum       : float -> 'a -> float -> 'a -> 'a -> unit;
    nvconst           : float -> 'a -> unit;
    nvprod            : 'a -> 'a -> 'a -> unit;
    nvdiv             : 'a -> 'a -> 'a -> unit;
    nvscale           : float -> 'a -> 'a -> unit;
    nvabs             : 'a -> 'a -> unit;
    nvinv             : 'a -> 'a -> unit;
    nvaddconst        : 'a -> float -> 'a -> unit;
    nvmaxnorm         : 'a -> float;
    nvwrmsnorm        : 'a -> 'a -> float;
    nvmin             : 'a -> float;

    nvdotprod         : ('a -> 'a -> float) option;
    nvcompare         : (float -> 'a -> 'a -> unit) option;
    nvinvtest         : ('a -> 'a -> bool) option;

    nvwl2norm         : ('a -> 'a -> float) option;
    nvl1norm          : ('a -> float) option;
    nvwrmsnormmask    : ('a -> 'a -> 'a -> float) option;
    nvconstrmask      : ('a -> 'a -> 'a -> bool) option;
    nvminquotient     : ('a -> 'a -> float) option;
  }

  external make_nvector : 'a nvector_ops -> 'a -> 'a nvector
      = "ml_nvec_new"

  external nvector_data : 'a nvector -> 'a
      = "ml_nvec_data"

  let add_tracing msg ops =
    let pr s = print_string msg; print_endline s in
    let {
        nvclone           = nvclone;
        nvdestroy         = nvdestroy;
        nvspace           = nvspace;
        nvlinearsum       = nvlinearsum;
        nvconst           = nvconst;
        nvprod            = nvprod;
        nvdiv             = nvdiv;
        nvscale           = nvscale;
        nvabs             = nvabs;
        nvinv             = nvinv;
        nvaddconst        = nvaddconst;
        nvmaxnorm         = nvmaxnorm;
        nvwrmsnorm        = nvwrmsnorm;
        nvmin             = nvmin;

        nvdotprod         = nvdotprod;
        nvcompare         = nvcompare;
        nvinvtest         = nvinvtest;

        nvwl2norm         = nvwl2norm;
        nvl1norm          = nvl1norm;
        nvwrmsnormmask    = nvwrmsnormmask;
        nvconstrmask      = nvconstrmask;
        nvminquotient     = nvminquotient;
      } = ops
    in
    let fo f f' = match f with None -> None | Some f -> Some (f' f) in

    let tr_nvclone a = pr "nvclone"; nvclone a
    and tr_nvdestroy = fo nvdestroy (fun f -> fun a -> (pr "nvdestroy"; f a))
    and tr_nvspace = fo nvspace (fun f -> fun a -> (pr "nvspace"; f a))
    and tr_nvlinearsum a x b y z = pr "nvlinearsum"; nvlinearsum a x b y z
    and tr_nvconst c z = pr "nvconst"; nvconst c z
    and tr_nvprod x y z = pr "nvprod"; nvprod x y z
    and tr_nvdiv x y z = pr "nvdiv"; nvdiv x y z
    and tr_nvscale c x z = pr "nvscale"; nvscale c x z
    and tr_nvabs x z = pr "nvabs"; nvabs x z
    and tr_nvinv x z = pr "nvinv"; nvinv x z
    and tr_nvaddconst x b z = pr "nvaddconst"; nvaddconst x b z
    and tr_nvmaxnorm x = pr "nvmaxnorm"; nvmaxnorm x
    and tr_nvwrmsnorm x w = pr "nvwrmsnorm"; nvwrmsnorm x w
    and tr_nvmin x = pr "nvmin"; nvmin x
    and tr_nvdotprod = fo nvdotprod (fun f -> fun x y -> pr "nvdotprod"; f x y)
    and tr_nvcompare =
      fo nvcompare (fun f -> fun c x z -> pr "nvcompare"; f c x z)
    and tr_nvinvtest = fo nvinvtest (fun f -> fun x z -> pr "nvinvtest"; f x z)
    and tr_nvwl2norm = fo nvwl2norm (fun f -> fun x w -> pr "nvwl2norm"; f x w)
    and tr_nvl1norm = fo nvl1norm (fun f -> fun x -> pr "nvl1norm"; f x)
    and tr_nvwrmsnormmask =
      fo nvwrmsnormmask (fun f -> fun x w id -> pr "nvwrmsnormmask"; f x w id)
    and tr_nvconstrmask =
      fo nvconstrmask (fun f -> fun c x m -> pr "nvconstrmask"; f c x m)
    and tr_nvminquotient =
      fo nvminquotient (fun f -> fun n d -> pr "nvminquotient"; f n d)
    in
    {
        nvclone           = tr_nvclone;
        nvdestroy         = tr_nvdestroy;
        nvspace           = tr_nvspace;
        nvlinearsum       = tr_nvlinearsum;
        nvconst           = tr_nvconst;
        nvprod            = tr_nvprod;
        nvdiv             = tr_nvdiv;
        nvscale           = tr_nvscale;
        nvabs             = tr_nvabs;
        nvinv             = tr_nvinv;
        nvaddconst        = tr_nvaddconst;
        nvmaxnorm         = tr_nvmaxnorm;
        nvwrmsnorm        = tr_nvwrmsnorm;
        nvmin             = tr_nvmin;

        nvdotprod         = tr_nvdotprod;
        nvcompare         = tr_nvcompare;
        nvinvtest         = tr_nvinvtest;

        nvwl2norm         = tr_nvwl2norm;
        nvl1norm          = tr_nvl1norm;
        nvwrmsnormmask    = tr_nvwrmsnormmask;
        nvconstrmask      = tr_nvconstrmask;
        nvminquotient     = tr_nvminquotient;
     }

end

module Immutable = struct
  type 'a nvector_ops = {
    nvclone           : 'a -> 'a;
    nvdestroy         : ('a -> unit) option;
    nvspace           : ('a -> (int * int)) option;

    nvlinearsum       : float -> 'a -> float -> 'a -> 'a;
    nvconst           : float -> 'a;
    nvprod            : 'a -> 'a -> 'a;
    nvdiv             : 'a -> 'a -> 'a;
    nvscale           : float -> 'a -> 'a;
    nvabs             : 'a -> 'a;
    nvinv             : 'a -> 'a;
    nvaddconst        : 'a -> float -> 'a;

    nvmaxnorm         : 'a -> float;
    nvwrmsnorm        : 'a -> 'a -> float;
    nvmin             : 'a -> float;

    nvdotprod         : ('a -> 'a -> float) option;
    nvcompare         : (float -> 'a -> 'a) option;
    nvinvtest         : ('a -> 'a -> bool) option;

    nvwl2norm         : ('a -> 'a -> float) option;
    nvl1norm          : ('a -> float) option;
    nvwrmsnormmask    : ('a -> 'a -> 'a -> float) option;
    nvconstrmask      : ('a -> 'a -> 'a -> bool) option;
    nvminquotient     : ('a -> 'a -> float) option;
  }

  let from_immutable
    { nvclone = imm_nvclone;
      nvdestroy = imm_nvdestroy;
      nvspace = imm_nvspace;

      nvlinearsum = imm_nvlinearsum;
      nvconst = imm_nvconst;
      nvprod = imm_nvprod;
      nvdiv = imm_nvdiv;
      nvscale = imm_nvscale;
      nvabs = imm_nvabs;
      nvinv = imm_nvinv;
      nvaddconst = imm_nvaddconst;

      nvmaxnorm = imm_nvmaxnorm;
      nvwrmsnorm = imm_nvwrmsnorm;
      nvmin = imm_nvmin;

      nvdotprod = imm_nvdotprod;
      nvcompare = imm_nvcompare;
      nvinvtest = imm_nvinvtest;

      nvwl2norm = imm_nvwl2norm;
      nvl1norm = imm_nvl1norm;
      nvwrmsnormmask = imm_nvwrmsnormmask;
      nvconstrmask = imm_nvconstrmask;
      nvminquotient = imm_nvminquotient;
    } =
    let single_arg imm_f x rv = (rv := imm_f !x)
    and double_arg imm_f x y rv = (rv := imm_f !x !y)
    and single_arg_o f =
      match f with
      | None -> None
      | Some imm_f -> Some (fun rv -> imm_f !rv)

    and double_arg_o f =
      match f with
      | None -> None
      | Some imm_f -> Some (fun rv1 rv2 -> imm_f !rv1 !rv2)

    and triple_arg_o f =
      match f with
      | None -> None
      | Some imm_f -> Some (fun rv1 rv2 rv3 -> imm_f !rv1 !rv2 !rv3)
    in

    let m_nvclone rv  = ref (imm_nvclone !rv)

    and m_nvdestroy   = single_arg_o imm_nvdestroy
    and m_nvspace     = single_arg_o imm_nvspace

    and m_nvlinearsum a x b y z = (z := imm_nvlinearsum a !x b !y)

    and m_nvconst c z = (z := imm_nvconst c)
    and m_nvprod      = double_arg imm_nvprod
    and m_nvdiv       = double_arg imm_nvprod
    and m_nvscale c   = single_arg (imm_nvscale c)
    and m_nvabs       = single_arg imm_nvabs
    and m_nvinv       = single_arg imm_nvinv
    and m_nvaddconst x b z = (z := imm_nvaddconst !x b)
    and m_nvmaxnorm x = imm_nvmaxnorm !x
    and m_nvwrmsnorm x w  = imm_nvwrmsnorm !x !w
    and m_nvmin x     = imm_nvmin !x

    and m_nvdotprod   = double_arg_o imm_nvdotprod
    and m_nvcompare =
      match imm_nvcompare with
      | None -> None
      | Some imm_f -> Some (fun c x z -> z := imm_f c !x)
    and m_nvinvtest   = double_arg_o imm_nvinvtest

    and m_nvwl2norm      = double_arg_o imm_nvwl2norm
    and m_nvl1norm       = single_arg_o imm_nvl1norm
    and m_nvwrmsnormmask = triple_arg_o imm_nvwrmsnormmask
    and m_nvconstrmask   = triple_arg_o imm_nvconstrmask
    and m_nvminquotient  = double_arg_o imm_nvminquotient

    in
    {
      Mutable.nvclone        = m_nvclone;
      Mutable.nvdestroy      = m_nvdestroy;
      Mutable.nvspace        = m_nvspace;

      Mutable.nvlinearsum    = m_nvlinearsum;
      Mutable.nvconst        = m_nvconst;
      Mutable.nvprod         = m_nvprod;
      Mutable.nvdiv          = m_nvdiv;
      Mutable.nvscale        = m_nvscale;
      Mutable.nvabs          = m_nvabs;
      Mutable.nvinv          = m_nvinv;
      Mutable.nvaddconst     = m_nvaddconst;

      Mutable.nvmaxnorm      = m_nvmaxnorm;
      Mutable.nvwrmsnorm     = m_nvwrmsnorm;
      Mutable.nvmin          = m_nvmin;

      Mutable.nvdotprod      = m_nvdotprod;
      Mutable.nvcompare      = m_nvcompare;
      Mutable.nvinvtest      = m_nvinvtest;

      Mutable.nvwl2norm      = m_nvwl2norm;
      Mutable.nvl1norm       = m_nvl1norm;
      Mutable.nvwrmsnormmask = m_nvwrmsnormmask;
      Mutable.nvconstrmask   = m_nvconstrmask;
      Mutable.nvminquotient  = m_nvminquotient;
    }

  let make_nvector ops = Mutable.make_nvector (from_immutable ops)
  let nvector_data v = !(Mutable.nvector_data v)
end


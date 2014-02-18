(*
 * Implementation in Ocaml of the Simulink Lookup Table (1-D and 2-D) blocks.
 *
 * Features:
 * - provides five 'Lookup methods':
 *       Interpolation-Extrapolation   (linear interpolation)
 *       Interpolation-Use End Values  (linear interpolation)
 *       Use Input Nearest
 *       Use Input Below
 *       Use Input Above
 * - provides three index search methods:
 *       binary, linear, evenly-spaced
 *   with the option to us the 'previous index result' for the first two.
 *
 * Limitations:
 * - No cublic spline interpolation.
 *)

module MkGetIdx =
  struct

  (* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
   * getidx functions *)

  (* Produce a function that returns an index to the breakpoint immediately
   * below the given value.
   * Return -1 if below the first value.
   * Return (Array.length breakpoints) if strictly larger than the last value.
   *
   * The variations below reflect different Simulink options for table lookup
   * blocks.
   *)

  let linear breakpoints =
    let len = Array.length breakpoints in
    let rec f i x =
      if i = len then i - 1
      else if x < breakpoints.(i) then i - 1
      else f (i + 1) x
    in f 0

  (* memorize the last lookup index with a reference cell, and begin searching
   * from it at the next call *)
  let linear_with_memory breakpoints =
    let len = Array.length breakpoints
    and i = ref 0
    in
    let f x =
      let rec fdown () =
        if !i = 0 then -1
        else (decr i; if x >= breakpoints.(!i) then !i else fdown ())
      in
      let rec fup () =
        if x = breakpoints.(!i) then !i
        else
          let i' = !i + 1 in
            if i' = len then len
            else if x < breakpoints.(i') then !i
            else (i := i'; fup ())
      in
      if x < breakpoints.(!i) then fdown () else fup ()
    in
    f

  (* use a binary search to find the most appropriate breakpoint index *)

  let bsearch breakpoints x =
    let rec search l u =
      (* invariant: x <= breakpoints.(u) *)
      if x < breakpoints.(l) then l - 1
      (* invariant: x >= breakpoints.(l) *)
      else if x >= breakpoints.(u) then u
      (* invariant: x < breakpoints.(u) *)
      else
        let mid = (l + u) / 2 in
        if x <= breakpoints.(mid) then search l mid else search (mid + 1) u
    in
    search

  let binary_search breakpoints =
    let lastidx = Array.length breakpoints - 1 in
    let search = bsearch breakpoints in
    let f x =
      if x > breakpoints.(lastidx) then lastidx + 1
      else search x 0 lastidx
    in
    f

  let binary_search_with_memory breakpoints =
    let lastidx = Array.length breakpoints - 1 in
    let midpoint = lastidx / 2 in
    let i = ref midpoint in
    let search = bsearch breakpoints in
    let update i' =
      ((if (0 <= i' && i' <= lastidx) then i := i' else i := midpoint); i')
    in
    let f x =
      update
      (if x > breakpoints.(!i) then
         (if x > breakpoints.(lastidx) then lastidx + 1
          else search x !i lastidx)
       else search x 0 !i)
    in
    f

  end

type lookupty = LinearLookup
              | BinaryLookup

let make_getidx ty = match ty with
    (LinearLookup, false) -> MkGetIdx.linear
  | (LinearLookup, true) -> MkGetIdx.linear_with_memory
  | (BinaryLookup, false) -> MkGetIdx.binary_search
  | (BinaryLookup, true) -> MkGetIdx.binary_search_with_memory

module type BREAKPOINT_TYPE =
  sig
    type t 

    val zero : t
    val one : t

    val to_int : t -> int (* must truncate *)
    val of_int : int -> t

    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val div : t -> t -> t
    val abs : t -> t
    val modulo : t -> t -> t

  end

module type WORKING_TYPE =
  sig
    type t 

    val zero : t
    val one : t

    val add : t -> t -> t
    val sub : t -> t -> t
    val mul : t -> t -> t
    val div : t -> t -> t

    val to_int : t -> int
    val of_int : int -> t
    val to_string : t -> string
  end

exception EmptyBreakpoints
exception NonmonotonicBreakpoints
exception BreakpointsDifferFromTableDimension
exception TooFewValuesForDimension

type interpolatety =
    InputBelow
  | InputAbove
  | Nearest
  | LinearInterpolation of bool (* true: extrapolation, false: end_values *)
  | CubicInterpolation of bool (* true: extrapolation, false: end_values *)

let input_below = InputBelow
let input_above = InputAbove
let nearest = Nearest
let linear_interpolation extrapolate = LinearInterpolation extrapolate
let cubic_interpolation extrapolate = CubicInterpolation extrapolate

type ('bpt, 'input, 'intern) breakpoint_lookup =
  {
    length : 'bpt -> int;
    check : 'bpt -> unit;

    use_input_below : 'bpt -> 'input -> int;
    use_input_above : 'bpt -> 'input -> int;
    use_input_nearest : 'bpt -> 'input -> int;

    interpol_extrapol : 'bpt -> 'input -> int * ('intern * 'intern * 'intern);
    interpol_endvalues : 'bpt -> 'input -> int * ('intern * 'intern * 'intern);

    round_up : 'intern * 'intern * 'intern;
    round_down : 'intern * 'intern * 'intern;
  }

module MkEvenlySpacedBreakpointsFn
  (I : WORKING_TYPE)
  (B : BREAKPOINT_TYPE)
  (BI : sig
          val btoi : B.t -> I.t
          val itob : I.t -> B.t
        end)
  :
  sig
    type bpt = { first : B.t; spacing : B.t; number : int; }
    val make_breakpoint_lookup :
      ('a -> I.t) -> ('a -> B.t) -> (bpt, 'a, I.t) breakpoint_lookup
    val is_evenlyspaced : B.t array -> bpt option
  end
  =
  struct
    type bpt = { first : B.t; spacing : B.t; number : int }

    let use_input_below es =
      let lastidx = es.number - 1 in
      let f xb =
        if xb <= es.first then 0
        else min lastidx (B.to_int (B.div (B.sub xb es.first) es.spacing))
      in
      f

    let use_input_above es =
      let lastidx = es.number - 1 in
      let f xb =
        if xb < es.first then 0
        else
          let x_shifted = B.sub xb es.first in
          let idx = B.to_int (B.div x_shifted es.spacing) in
          min lastidx
            (if B.modulo x_shifted es.spacing = B.zero then idx else idx + 1)
      in
      f

    let use_input_nearest es =
      let lastidx = es.number - 1 in
      let halfspacing = (B.div es.spacing (B.add B.one B.one)) in
      let f xb =
        if xb < es.first then 0
        else
          let x_shifted = B.sub xb es.first in
          let idx = B.to_int (B.div x_shifted es.spacing)
          and rdown = B.abs (B.modulo x_shifted es.spacing) <= halfspacing in
          min lastidx (if rdown then idx else idx + 1)
      in
      f

    let round_down = (I.one, I.zero, I.one)
    let round_up = (I.one, I.one, I.zero)

    let interpol_extrapol intoi intob es =
      let lastidx = es.number - 1 in
      let bp0 = BI.btoi es.first
      and bp1 = BI.btoi (B.add es.first es.spacing)
      and bpl' = B.add es.first (B.mul (B.of_int lastidx) es.spacing) in
      let bpl = BI.btoi bpl'
      and bp2l = BI.btoi
        (B.add es.first (B.mul (B.of_int (lastidx - 1)) es.spacing))
      and spacingi = BI.btoi es.spacing
      and firsti = BI.btoi es.first
      in
      let f x =
        let x = intoi x
        and xb = intob x in
        if xb < es.first
          then (0, (spacingi, I.sub x bp0, I.sub bp1 x))
        else if xb >= bpl'
          then (lastidx - 1, (spacingi, I.sub x bp2l, I.sub bpl x))
        else
          let idx = B.to_int (B.div (B.sub xb es.first) es.spacing) in
          let leftdist =
            I.sub x (I.add firsti (I.mul (I.of_int idx) spacingi))
          in
          (idx, (spacingi, leftdist, I.sub spacingi leftdist))
      in
      f

    let interpol_endvalues intoi intob es =
      let lastidx = es.number - 1 in
      let bpl = B.add es.first (B.mul (B.of_int lastidx) es.spacing)
      and spacingi = BI.btoi es.spacing
      and firsti = BI.btoi es.first
      in
      let f x =
        let x = intoi x
        and xb = intob x in
        if xb < es.first then (0, round_down)
        else if xb >= bpl then (lastidx - 1, round_up)
        else
          let idx = B.to_int (B.div (B.sub xb es.first) es.spacing) in
          let leftdist = I.sub x (I.add firsti (I.mul (I.of_int idx) spacingi))
          in
          (idx, (spacingi, leftdist, I.sub spacingi leftdist))
        in
        f

    let make_breakpoint_lookup intoi intob =
      let map_input f b x = f b (intob x) in
      {
        length = (fun bps -> bps.number);
        check = (fun x -> ());

        round_up = round_up;
        round_down = round_down;

        use_input_below = map_input use_input_below;
        use_input_above = map_input use_input_above;
        use_input_nearest = map_input use_input_nearest;

        interpol_extrapol = interpol_extrapol intoi intob;
        interpol_endvalues = interpol_endvalues intoi intob;
      }

    let is_evenlyspaced breakpoints =
      let number = Array.length breakpoints in
      if number = 1 then
        Some { first = breakpoints.(0); spacing = B.zero; number = 1 }
      else
        let first = breakpoints.(0) in
        let spacing = B.sub breakpoints.(1) first in

        let rec check last idx =
          if idx = number then
            Some { first = first; spacing = spacing; number = number }
          else if (B.sub breakpoints.(idx) last) <> spacing then None
          else check breakpoints.(idx) (idx + 1)
        in
        check first 1

  end

module MkArrayBreakpointsFn
  (I : WORKING_TYPE)
  :
  sig
    val make_breakpoint_lookup :
      lookupty * bool ->
      ('a -> I.t) ->
      ('a -> 'b) ->
      ('b -> I.t) ->
      ('b array, 'a, I.t) breakpoint_lookup
  end
  =
  struct
    type input_t

    let length = Array.length

    let check_monotonic last curr =
      if (curr < last) then
        raise NonmonotonicBreakpoints
      else curr

    let check breakpoints =
      let number = Array.length breakpoints in
      if number = 0 then raise EmptyBreakpoints
      else
        ignore (Array.fold_left check_monotonic breakpoints.(0) breakpoints)

    let use_input_below breakpoints =
      let lastidx = Array.length breakpoints - 1 in
      let f idx =
        if idx >= lastidx then lastidx
        else max 0 idx
      in
      f

    let use_input_above breakpoints =
      let lastidx = Array.length breakpoints - 1 in
      let f (idx, xb) =
        if idx >= lastidx then lastidx
        else if idx = -1 then 0
        else if (xb > breakpoints.(idx)) then idx + 1
        else idx
      in
      f

    let use_input_nearest btoi breakpoints =
      let lastidx = Array.length breakpoints - 1 in
      let f (idx, x) =
        if idx = -1 then 0
        else if idx >= lastidx then lastidx
        else
          let dl = I.sub x (btoi breakpoints.(idx)) in
          let du = I.sub (btoi breakpoints.(idx + 1)) x in
          if dl <= du then idx else idx + 1
      in
      f

    (* Simulink: Interpolation-Extrapolation *)

    let interpol_extrapol btoi breakpoints =
      let lastidx = Array.length breakpoints - 1 in
      let bp0 = btoi breakpoints.(0)
      and bp1 = btoi breakpoints.(1)
      and bpl = btoi breakpoints.(lastidx)
      and bp2l = btoi breakpoints.(lastidx - 1)
      in
      let ldistance = I.sub bp1 bp0
      and udistance = I.sub bpl bp2l
      in
      let f (idx, x) =
        if idx = -1 then (0, (ldistance, I.sub x bp0, I.sub bp1 x))
        else if idx >= lastidx
             then (lastidx - 1, (udistance, I.sub x bp2l, I.sub bpl x))
        else
          let bpidx = btoi breakpoints.(idx)
          and bpidx' = btoi breakpoints.(idx + 1)
          in
          let d = I.sub bpidx' bpidx in
          (idx, (d, I.sub x bpidx, I.sub bpidx' x))
      in
      f

    (* Simulink: Interpolation-Use End Values *)

    let round_down = (I.one, I.zero, I.one)
    let round_up = (I.one, I.one, I.zero)

    let interpol_endvalues btoi breakpoints =
      let lastidx = Array.length breakpoints - 1 in
      let f (idx, x) =
        if idx = -1 then (0, round_down)
        else if idx >= lastidx then (lastidx - 1, round_up)
        else
          let bpidx = btoi breakpoints.(idx)
          and bpidx' = btoi breakpoints.(idx + 1)
          in
          let d = I.sub bpidx' bpidx in
          (idx, (d, I.sub x bpidx, I.sub bpidx' x))
      in
      f

    let make_breakpoint_lookup indexlookup intoi intob btoi =
      let get_idx = make_getidx indexlookup in

      let couple f arr x = f arr (get_idx arr (intob x))
      and couple' f arr x = f arr ((get_idx arr (intob x)), intob x)
      and couple'' f arr x = f arr ((get_idx arr (intob x)), intoi x)
      in
      {
        length = Array.length;
        check = check;

        round_up = round_up;
        round_down = round_down;

        use_input_below = couple use_input_below;
        use_input_above = couple' use_input_above;
        use_input_nearest = couple'' (use_input_nearest btoi);

        interpol_extrapol = couple'' (interpol_extrapol btoi);
        interpol_endvalues = couple'' (interpol_endvalues btoi);
      }

  end

module MkBreakpointsFn
  (I : WORKING_TYPE)
  (B : BREAKPOINT_TYPE)
  (BI : sig
          val btoi : B.t -> I.t
          val itob : I.t -> B.t
        end)
  :
  sig
    val make_breakpoint_lookup :
      lookupty * bool ->
      ('a -> I.t) ->
      ('a -> B.t) ->
      (B.t -> I.t) ->
      (B.t array, 'a, I.t) breakpoint_lookup
  end
  =
  struct
    module EvenBPs = MkEvenlySpacedBreakpointsFn (I) (B) (BI)
    module ArrayBPs = MkArrayBreakpointsFn (I)

    let make_breakpoint_lookup indexlookup intoi intob btoi =
      let array_bpl =
        ArrayBPs.make_breakpoint_lookup indexlookup intoi intob btoi
      and even_bpl = EvenBPs.make_breakpoint_lookup intoi intob
      in
      let choosef arrf evenf bpt =
        match EvenBPs.is_evenlyspaced bpt with
          None -> arrf bpt
        | Some esbpt -> evenf esbpt
      in
      {
        length = array_bpl.length;
        check = array_bpl.check;

        use_input_below = choosef array_bpl.use_input_below
                                  even_bpl.use_input_below;
        use_input_above = choosef array_bpl.use_input_above
                                  even_bpl.use_input_above;
        use_input_nearest = choosef array_bpl.use_input_nearest
                                    even_bpl.use_input_nearest;

        interpol_extrapol = choosef array_bpl.interpol_extrapol
                                    even_bpl.interpol_extrapol;
        interpol_endvalues = choosef array_bpl.interpol_endvalues
                                     even_bpl.interpol_endvalues;

        round_up = array_bpl.round_up;
        round_down = array_bpl.round_down;
      }
  end

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * lookup functions *)

let make_idx_lookup bpl = function
    InputBelow -> bpl.use_input_below
  | InputAbove -> bpl.use_input_above
  | Nearest    -> bpl.use_input_nearest
  | _          -> failwith "make_idx_lookup: bad call"

let make_idx_inter_lookup bpl interpolation bps =
  let lastidx = bpl.length bps
  and lookup = make_idx_lookup bpl interpolation bps
  in
  (fun x ->
    let idx = lookup x in
    if idx = lastidx then (idx - 1, bpl.round_up)
    else (idx, bpl.round_down))

let make_inter_lookup bpl interpolation bps =
  match interpolation with
    InputBelow | InputAbove | Nearest ->
      make_idx_inter_lookup bpl interpolation bps
  | LinearInterpolation false -> 
      bpl.interpol_endvalues bps
  | LinearInterpolation true ->
      bpl.interpol_extrapol bps
  | CubicInterpolation _ -> failwith "cubic interpolation is not implemented"

module type LOOKUP_TABLE_1D =
  sig
    type 'a t

    val dim : 'a t -> int
    val get : 'a t -> int -> 'a
  end

module type LOOKUP_TABLE_2D =
  sig
    type 'a t

    val dim1 : 'a t -> int
    val dim2 : 'a t -> int
    val get : 'a t -> int -> int -> 'a
  end

module LookupFn
  (I : WORKING_TYPE)
  (LT1 : LOOKUP_TABLE_1D)
  (LT2 : LOOKUP_TABLE_2D)
  =
  struct

    let one_d lookupfn f =
      let lf x =
        let (x1idx, (x2_x1, x_x1, x2_x)) = lookupfn x in
        let x2idx = x1idx + 1 in
        let f_x1idx = f x1idx in
        I.add f_x1idx (I.mul (I.div x_x1 x2_x1) (I.sub (f x2idx) f_x1idx))
      in
      lf

    (* Take a function that takes a breakpoint index (returned by a getidx
     * function) and a value and returns:
     * - an adjusted breakpoint index
     * - the distance between that breakpoint and the next:  (x2 - x1)
     * - the distance from that breakpoint and the value:    (x - x1)
     * - the distance from the value to the next breakpoint: (x2 - x)
     *         
     *         |       .             |
     *        x1       x             x2
     *      (idx)                 (idx + 1)
     *)

    let two_d lookupfn1 lookupfn2 f =
      let lf (x, y) =
        let (x1, (x2_x1, x_x1, x2_x)) = lookupfn1 x
        and (y1, (y2_y1, y_y1, y2_y)) = lookupfn2 y
        in
        let (x2, y2) = (x1 + 1, y1 + 1)
        and x2x1_y2y1 = I.mul x2_x1 y2_y1 
        in
        let r11 = I.mul (I.mul (I.div (f(x1, y1)) x2x1_y2y1) x2_x) y2_y
        and r21 = I.mul (I.mul (I.div (f(x2, y1)) x2x1_y2y1) x_x1) y2_y
        and r12 = I.mul (I.mul (I.div (f(x1, y2)) x2x1_y2y1) x2_x) y_y1
        and r22 = I.mul (I.mul (I.div (f(x2, y2)) x2x1_y2y1) x_x1) y_y1
        in
        I.add (I.add (I.add r11 r21) r12) r22
      in
      lf

    let make_lookup_1d bpl interp bps table ttoi =
      let table_f x = ttoi (LT1.get table x) in
      bpl.check bps;
      if bpl.length bps <> LT1.dim table then
        raise BreakpointsDifferFromTableDimension
      else
        match interp with
          InputBelow | InputAbove | Nearest ->
            let l = make_idx_lookup bpl interp bps in
            (fun x -> ttoi (LT1.get table (l x)))

        | LinearInterpolation _ ->
            let l = make_inter_lookup bpl interp bps in
            one_d l table_f

        | CubicInterpolation _ ->
            failwith "cubic interpolation is not implemented"

    let make_lookup_2d bpl1 bpl2 interp1 interp2 bps1 bps2 table ttoi =
      let table_f (x, y) = ttoi (LT2.get table x y) in
      bpl1.check bps1; bpl2.check bps2;
      if (bpl1.length bps1 <> LT2.dim1 table ||
          bpl2.length bps2 <> LT2.dim2 table)
      then raise BreakpointsDifferFromTableDimension
      else
        let lookup1 = make_inter_lookup bpl1 interp1 bps1
        and lookup2 = make_inter_lookup bpl2 interp2 bps2
        in
        two_d lookup1 lookup2 table_f

  end

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * test functions *)

module TestFn
  (I : WORKING_TYPE)
  =
  struct

    let test_1d (start, inc, final) itoin fout f =
      let outp x =
        let xf = I.add start (I.mul (I.of_int x) inc) in
        Printf.fprintf fout "\t%s\t%s\n"
          (I.to_string xf)
          (I.to_string (f (itoin xf)))
      and x = ref 0
      and max_x = I.to_int (I.div (I.sub final start) inc)
      in
      Printf.fprintf fout "#\tx\ty\n";
      while (!x <= max_x) do
        outp !x; incr x
      done;
      flush fout

    let test_2d
      (start1, inc1, final1) itoin1
      (start2, inc2, final2) itoin2
      fout f
      =
      let outp x y =
        let xf = I.add start1 (I.mul (I.of_int x) inc1)
        and yf = I.add start2 (I.mul (I.of_int y) inc2) in
        Printf.fprintf fout "\t%s\t%s\t%s\n"
            (I.to_string xf)
            (I.to_string yf)
            (I.to_string (f (itoin1 xf, itoin2 yf)))
      and x = ref 0
      and y = ref 0
      and max_x = I.to_int (I.div (I.sub final1 start1) inc1)
      and max_y = I.to_int (I.div (I.sub final2 start2) inc2)
      in
      Printf.fprintf fout "#\tx\ty\tz\n";
      while (!y <= max_y) do
        x := 0;
        while (!x <= max_x) do
          outp !x !y; incr x
        done;
        incr y
      done;
      flush fout

  end

module TestUtilFn
  (I : WORKING_TYPE)
  (B : BREAKPOINT_TYPE)
  (BI : sig
          val btoi : B.t -> I.t
          val itob : I.t -> B.t
        end)
  =
  struct

    let array_diff_fold_left f b arr =
      let acc = ref b in
      let rec iter idx =
        if idx >= Array.length arr then !acc
        else
          (acc := f (!acc) (I.sub (BI.btoi arr.(idx))
                                  (BI.btoi arr.(idx - 1)));
           iter (idx + 1))
      in iter 1

    let max m n = if m > n then m else n
    let min m n = if m < n then m else n

    let to_test_dist samples (breakpoints : B.t array) =
      let largest = array_diff_fold_left max I.zero breakpoints
      and f s d = if d > I.zero then min s d else s
      and two = I.add I.one I.one
      in
      let smallest = array_diff_fold_left f largest breakpoints in
      (I.sub (BI.btoi breakpoints.(0)) (I.mul two largest),
       I.div smallest (I.of_int samples),
       I.add (BI.btoi breakpoints.(Array.length breakpoints - 1))
             (I.mul two largest))

  end

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * Instantiations *)

let id x = x

module Float =
  struct
    type t = float

    let zero = 0.0
    let one = 1.0

    let add = (+.)
    let sub = (-.)
    let mul = ( *.)
    let div = (/.)

    let modulo = mod_float
    let abs = abs_float

    let to_int = int_of_float
    let of_int = float_of_int
    let to_string = Printf.sprintf "%.8f"
  end

module Integer =
  struct
    type t = int

    let zero = 0
    let one = 1

    let add = (+)
    let sub = (-)
    let mul x y = x * y
    let div = (/)

    let modulo = (mod)
    let abs = abs

    let to_int = id
    let of_int = id
    let to_string = string_of_int
  end

module StandardArray1d
  : LOOKUP_TABLE_1D with type 'a t = 'a array
  =
  struct
     type 'a t = 'a array
     let dim = Array.length
     let get = Array.get
  end

module StandardArray2d
  : LOOKUP_TABLE_2D with type 'a t = 'a array array
  =
  struct
     type 'a t = 'a array array
     let dim1 = Array.length
     let dim2 arr = Array.length arr.(0)
     let get arr x y = arr.(x).(y)
  end

(*
open Bigarray

module BigFloatArray1d : LookupTable1dType =
  struct
     type 'a t = ('a, ('a, float32_elt) kind, c_layout) Array1.t
     let dim = Array1.dim
     let get = Array1.get
  end

module BigFloatArray2d : LookupTable2dType =
  struct
     type 'a t = ('a, ('a, float32_elt) kind, c_layout) Array2.t
     let dim1 = Array2.dim1
     let dim2 = Array2.dim2
     let get = Array2.get
  end
*)

module IntegerBreakpoints = MkBreakpointsFn (Float) (Integer)
  (struct let btoi = float_of_int and itob = truncate end)

let make_int_breakpoint_lookup = IntegerBreakpoints.make_breakpoint_lookup


module ESIntegerBreakpoints = MkEvenlySpacedBreakpointsFn (Float) (Integer)
  (struct let btoi = float_of_int and itob = truncate end)

type regular_int_breakpoints = ESIntegerBreakpoints.bpt

let regular_int_breakpoints first spacing last =
  {
    ESIntegerBreakpoints.first = first;
    ESIntegerBreakpoints.spacing = spacing;
    ESIntegerBreakpoints.number =
      int_of_float (ceil ((float last -. float first) /. float spacing)) + 1
  }

let regular_int_breakpoints_lookup =
  ESIntegerBreakpoints.make_breakpoint_lookup
    (function x -> x)
    (int_of_float)


module FloatBreakpoints = MkBreakpointsFn (Float) (Float)
  (struct let btoi = id and itob = id end)

let make_float_breakpoint_lookup = FloatBreakpoints.make_breakpoint_lookup


module ESFloatBreakpoints = MkEvenlySpacedBreakpointsFn (Float) (Float)
  (struct let btoi = id and itob = id end)

type regular_float_breakpoints = ESFloatBreakpoints.bpt

let regular_float_breakpoints first spacing last =
  {
    ESFloatBreakpoints.first = first;
    ESFloatBreakpoints.spacing = spacing;
    ESFloatBreakpoints.number = int_of_float (ceil ((last -. first) /. spacing)) + 1
  }

let regular_float_breakpoints_lookup =
  ESFloatBreakpoints.make_breakpoint_lookup
    (function x -> x)
    (function x -> x)


module FloatLookup = LookupFn (Float) (StandardArray1d) (StandardArray2d)

let float_make_lookup_1d = FloatLookup.make_lookup_1d
let float_make_lookup_2d = FloatLookup.make_lookup_2d

module IntegerLookup = LookupFn (Integer) (StandardArray1d) (StandardArray2d)

let int_make_lookup_1d = IntegerLookup.make_lookup_1d
let int_make_lookup_2d = IntegerLookup.make_lookup_2d

module FloatTest = TestFn (Float)

let test_1d = FloatTest.test_1d
let test_2d = FloatTest.test_2d

module IntegerTestUtil = TestUtilFn (Float) (Integer)
  (struct let btoi = float_of_int and itob = truncate end)
module FloatTestUtil = TestUtilFn (Float) (Float)
  (struct let btoi = id and itob = id end)

let int_breakpoints lookup =
  make_int_breakpoint_lookup
    lookup
    (function x -> x)
    (int_of_float)
    (float_of_int)

let float_breakpoints lookup =
  make_float_breakpoint_lookup
    lookup
    (function x -> x)
    (function x -> x)
    (function x -> x)

let int_breakpoints_to_test_dist = IntegerTestUtil.to_test_dist
let float_breakpoints_to_test_dist = FloatTestUtil.to_test_dist

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * tests *)

(*
let bps = [|
    10.;
    12.;
    25.;
    40.;
|]

let table = [|
    100.;
    120.;
    250.;
    400.;
|]

let array_linear_lookup
  = FloatBreakpoints.make_breakpoint_lookup (LinearLookup, false) id id id
let array_linear_lookup_with_memory
  = FloatBreakpoints.make_breakpoint_lookup (LinearLookup, true) id id id

let array_binary_lookup
  = FloatBreakpoints.make_breakpoint_lookup (BinaryLookup, false) id id id
let array_binary_lookup_with_memory
  = FloatBreakpoints.make_breakpoint_lookup (BinaryLookup, true) id id id

let run_test_1d' filename f =
  let outp = open_out filename in
  (FloatTest.test_1d (0., 0.1, 100.) id outp f;
   close_out outp)

let run_test_1d filename bps f =
  let outp = open_out filename in
  (FloatTest.test_1d (float_breakpoints_to_test_dist 10 bps) id outp f;
   close_out outp)

let run_below () = run_test_1d' "below.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup InputBelow bps table id)

let run_above () = run_test_1d' "above.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup InputAbove bps table id)

let run_nearest () = run_test_1d' "nearest.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup Nearest bps table id)

let run_inter_extra () = run_test_1d' "inter-extra.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup (LinearInterpolation true) bps table id)

let run_inter_endval () = run_test_1d' "inter-endval.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup (LinearInterpolation false) bps table id)

let run_binary_lookup () = run_test_1d' "binary-lookup.log"
  (FloatLookup.make_lookup_1d
    array_binary_lookup InputBelow bps table id)

let run_memory_lookup () = run_test_1d' "memory-lookup.log"
  (FloatLookup.make_lookup_1d
    array_linear_lookup_with_memory (LinearInterpolation true) bps table id)

let run_binary_memory_lookup () = run_test_1d' "binary-memory-lookup.log"
  (FloatLookup.make_lookup_1d
    array_binary_lookup_with_memory InputBelow bps table id)

let run_autopoints_lookup () = run_test_1d "autopoints-lookup.log" bps
  (FloatLookup.make_lookup_1d
    array_linear_lookup_with_memory (LinearInterpolation true) bps table id)

let _ = run_below ()
let _ = run_above ()
let _ = run_nearest ()
let _ = run_inter_extra ()
let _ = run_inter_endval ()
let _ = run_binary_lookup ()
let _ = run_memory_lookup ()
let _ = run_binary_memory_lookup ()
let _ = run_autopoints_lookup ()
*)


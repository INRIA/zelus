type lookupty = LinearLookup | BinaryLookup

val make_getidx : lookupty * bool -> 'a array -> 'a -> int

module type BREAKPOINT_TYPE =
  sig
    type t
    val zero : t
    val one : t
    val to_int : t -> int
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
  | LinearInterpolation of bool
  | CubicInterpolation of bool

type ('bpt, 'input, 'intern) breakpoint_lookup

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
      ('a -> I.t) ->
      ('a -> B.t) ->
      (bpt, 'a, I.t) breakpoint_lookup

    val is_evenlyspaced : B.t array -> bpt option
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
  :
  sig
    val make_lookup_1d :
      ('a, 'b, I.t) breakpoint_lookup ->
      interpolatety ->
      'a ->
      'c LT1.t ->
      ('c -> I.t) ->
      'b -> I.t

    val make_lookup_2d :
      ('a, 'b, I.t) breakpoint_lookup ->
      ('c, 'd, I.t) breakpoint_lookup ->
      interpolatety ->
      interpolatety ->
      'a ->
      'c ->
      'e LT2.t ->
      ('e -> I.t) ->
      'b * 'd -> I.t
  end

module TestFn
  (I : WORKING_TYPE)
  :
  sig
    val test_1d :
      I.t * I.t * I.t ->
      (I.t -> 'a) ->
      out_channel ->
      ('a -> I.t) ->
      unit

    val test_2d :
      I.t * I.t * I.t ->
      (I.t -> 'a) ->
      I.t * I.t * I.t ->
      (I.t -> 'b) ->
      out_channel ->
      ('a * 'b -> I.t) -> unit
  end

module TestUtilFn
  (I : WORKING_TYPE)
  (B : BREAKPOINT_TYPE)
  (BI : sig
          val btoi : B.t -> I.t
          val itob : I.t -> B.t
        end)
  :
  sig
    val to_test_dist : int -> B.t array -> I.t * I.t * I.t
  end

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * Instantiations *)

val make_float_breakpoint_lookup :
  lookupty * bool ->
  ('a -> float) ->
  ('a -> float) ->
  (float -> float) ->
  (float array, 'a, float) breakpoint_lookup


type regular_float_breakpoints

val regular_float_breakpoints :
  float ->
  float ->
  float ->
  regular_float_breakpoints

val regular_float_breakpoints_lookup :
  (regular_float_breakpoints, float, float) breakpoint_lookup


val make_int_breakpoint_lookup :
  lookupty * bool ->
  ('a -> float) ->
  ('a -> int) ->
  (int -> float) ->
  (int array, 'a, float) breakpoint_lookup


type regular_int_breakpoints

val regular_int_breakpoints :
  int ->
  int ->
  int ->
  regular_int_breakpoints

val regular_int_breakpoints_lookup :
  (regular_int_breakpoints, float, float) breakpoint_lookup

val float_make_lookup_1d :
  ('a, 'b, float) breakpoint_lookup ->
  interpolatety ->
  'a ->
  'c array ->
  ('c -> float) ->
  'b -> float

val float_make_lookup_2d :
  ('a, 'b, float) breakpoint_lookup ->
  ('c, 'd, float) breakpoint_lookup ->
  interpolatety ->
  interpolatety ->
  'a ->
  'c ->
  'e array array ->
  ('e -> float) ->
  'b * 'd -> float

val int_make_lookup_1d :
  ('a, 'b, int) breakpoint_lookup ->
  interpolatety ->
  'a ->
  'c array ->
  ('c -> int) ->
  'b -> int

val int_make_lookup_2d :
  ('a, 'b, int) breakpoint_lookup ->
  ('c, 'd, int) breakpoint_lookup ->
  interpolatety ->
  interpolatety ->
  'a ->
  'c ->
  'e array array ->
  ('e -> int) ->
  'b * 'd -> int

val test_1d :
  float * float * float ->
  (float -> 'a) ->
  out_channel ->
  ('a -> float) ->
  unit

val test_2d :
  float * float * float ->
  (float -> 'a) ->
  float * float * float ->
  (float -> 'b) ->
  out_channel ->
  ('a * 'b -> float) ->
  unit

val int_breakpoints :
  lookupty * bool -> (int array, float, float) breakpoint_lookup
val float_breakpoints :
  lookupty * bool -> (float array, float, float) breakpoint_lookup

val int_breakpoints_to_test_dist : int -> int array -> float * float * float
val float_breakpoints_to_test_dist : int -> float array -> float * float * float


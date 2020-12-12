(* Dual numbers, used for automatic differentiation *)
(* Added by B. Caillaud <benoit.caillaud@inria.fr> *)

type float = Dual.t

(* the core module. taken from Ocaml *)
(* pour debugger set arguments -nopervasives -i lib/pervasives.lsi *)

(* Every occurrence of type float has been replaced by type dual *) 

(* val ( = ) : 'a * 'a -> bool *)

let ( = ) = Pervasives.( = )

(* val ( <> ) : 'a * 'a -> bool *)

let ( <> ) = Pervasives.( <> )

(* val ( < ) : 'a * 'a -> bool *)

let ( < ) = Pervasives.( < )

(* val ( > ) : 'a * 'a -> bool *)

let ( > ) = Pervasives.( > )

(* val ( <= ) : 'a * 'a -> bool *)

let ( <= ) = Pervasives.( <= )

(* val ( >= ) : 'a * 'a -> bool *)

let ( >= ) = Pervasives.( >= )

(* val compare : 'a * 'a -> int *)

let compare = Pervasives.compare

(* val min : 'a * 'a -> 'a *)

let min = Pervasives.min

(* val max : 'a * 'a -> 'a *)

let max = Pervasives.max

(* val ( == ) : 'a * 'a -> bool *)

let ( == ) = Pervasives.( == )

(* val ( != ) : 'a * 'a -> bool *)

let ( != ) = Pervasives.( != )

(* val not : bool -> bool *)

let not = Pervasives.not

(* val ( && ) : bool * bool -> bool *)

let ( && ) = Pervasives.( && )

(* val ( & ) : bool * bool -> bool *)

let ( & ) = Pervasives.( & )

(* val ( || ) : bool * bool -> bool *)

let ( || ) = Pervasives.( || )

(* val ( or ) : bool * bool -> bool *)

let ( or ) = Pervasives.( or )

(* val ( ~- ) : int -> int *)

let ( ~- ) = Pervasives.( ~- )

(* val succ : int -> int *)

let succ = Pervasives.succ

(* val pred : int -> int *)

let pred = Pervasives.pred

(* val ( + ) : int * int -> int *)

let ( + ) = Pervasives.( + )

(* val ( - ) : int * int -> int *)

let ( - ) = Pervasives.( - )

(* val ( * ) : int * int -> int *)

let ( * ) = Pervasives.( * )

(* val ( / ) : int * int -> int *)

let ( / ) = Pervasives.( / )

(* val ( mod ) : int * int -> int *)

let ( mod ) = Pervasives.( mod )

(* val abs : int -> int *)

let abs = Pervasives.abs

(* val max_int : int *)

let max_int = Pervasives.max_int

(* val min_int : int *)

let min_int = Pervasives.min_int

(* val ( land ) : int * int -> int *)

let ( land ) = Pervasives.( land )

(* val ( lor ) : int * int -> int *)

let ( lor ) = Pervasives.( lor )

(* val ( lxor ) : int * int -> int *)

let ( lxor ) = Pervasives.( lxor )

(* val lnot : int -> int *)

let lnot = Pervasives.lnot

(* val ( lsl ) : int * int -> int *)

let ( lsl ) = Pervasives.( lsl )

(* val ( lsr ) : int * int -> int *)

let ( lsr ) = Pervasives.( lsr )

(* val ( asr ) : int * int -> int *)

let ( asr ) = Pervasives.( asr )

(* val ( ~-. ) : float -> float *)

let ( ~-. ) = Dual.( ~-. )

(* val ( +. ) : float * float -> float *)

let ( +. ) = Dual.( +. )

(* val ( -. ) : float * float -> float *)

let ( -. ) = Dual.( -. )

(* val ( *. ) : float * float -> float *)

let ( *. ) = Dual.( *. )

(* val ( /. ) : float * float -> float *)

let ( /. ) = Dual.( /. )

(* val ( ** ) : float * float -> float *)

let ( ** ) = Dual.( ** )

(* val sqrt : float -> float *)

let sqrt = Dual.sqrt

(* val exp : float -> float *)

let exp = Dual.exp

(* val log : float -> float *)

let log = Dual.log

(* val log10 : float -> float *)

let log10 = Dual.log10

(* val cos : float -> float *)

let cos = Dual.cos

(* val sin : float -> float *)

let sin = Dual.sin

(* val tan : float -> float *)

let tan = Dual.tan

(* val acos : float -> float *)

let acos = Dual.acos

(* val asin : float -> float *)

let asin = Dual.asin

(* val atan : float -> float *)

let atan = Dual.atan

(* val atan2 : float * float -> float *)

let atan2 = Dual.atan2

(* val cosh : float -> float *)

let cosh = Dual.cosh

(* val sinh : float -> float *)

let sinh = Dual.sinh

(* val tanh : float -> float *)

let tanh = Dual.tanh

(* val ceil : float -> float *)

let ceil = Dual.ceil

(* val floor : float -> float *)

let floor = Dual.floor

(* val abs_float : float -> float *)

let abs_float = Dual.abs_float

(* val mod_float : float * float -> float *)

let mod_float = Dual.mod_float

(* val frexp : float -> float * int *)

let frexp = Dual.frexp

(* val ldexp : float * int -> float *)

let ldexp = Dual.ldexp

(* val modf : float -> float * float *)

let modf = Dual.modf

(* val float : int -> float *)

let float = Dual.float

(* val float_of_int : int -> float *)

let float_of_int = Dual.float_of_int

(* val truncate : float -> int *)

let truncate = Dual.truncate

(* val int_of_float : float -> int *)

let int_of_float = Dual.int_of_float

(* val infinity : float *)

let infinity = Dual.infinity

(* val neg_infinity : float *)

let neg_infinity = Dual.neg_infinity

(* val nan : float *)

let nan = Dual.nan

(* val max_float : float *)

let max_float = Dual.max_float

(* val min_float : float *)

let min_float = Dual.min_float

(* val epsilon_float : float *)

let epsilon_float = Dual.epsilon_float

type fpclass = Pervasives.fpclass

(* val classify_float : float -> fpclass *)

let classify_float = Dual.classify_float

(* val ( ^ ) : string * string -> string *)

let ( ^ ) = Pervasives.( ^ )

(* val int_of_char : char -> int *)

let int_of_char = Pervasives.int_of_char

(* val char_of_int : int -> char *)

let char_of_int = Pervasives.char_of_int

(* val ignore : 'a -> unit *)

let ignore = Pervasives.ignore

(* val string_of_bool : bool -> string *)

let string_of_bool = Pervasives.string_of_bool

(* val bool_of_string : string -> bool *)

let bool_of_string = Pervasives.bool_of_string

(* val string_of_int : int -> string *)

let string_of_int = Pervasives.string_of_int

(* val int_of_string : string -> int *)

let int_of_string = Pervasives.int_of_string

(* val string_of_float : float -> string *)

let string_of_float = Dual.string_of_float

(* val float_of_string : string -> float *)

let float_of_string = Dual.float_of_string

(* val fst : 'a * 'b -> 'a *)

let fst = Pervasives.fst

(* val snd : 'a * 'b -> 'b *)

let snd = Pervasives.snd

type in_channel = Pervasives.in_channel
type out_channel = Pervasives.out_channel

(* val stdin : in_channel  *)

let stdin = Pervasives.stdin

(* val stdout : out_channel *)

let stdout = Pervasives.stdout

(* val stderr : out_channel  *)

let stderr = Pervasives.stderr

(* val print_char : char -> unit *)

let print_char = Pervasives.print_char

(* val print_string : string -> unit *)

let print_string = Pervasives.print_string

(* val print_int : int -> unit *)

let print_int = Pervasives.print_int

(* val print_float : float -> unit *)

let print_float = Dual.print_float

(* val print_endline : string -> unit *)

let print_endline = Pervasives.print_endline

(* val print_newline : unit -> unit *)

let print_newline = Pervasives.print_newline

(* val prerr_char : char -> unit *)

let prerr_char = Pervasives.prerr_char

(* val prerr_string : string -> unit *)

let prerr_string = Pervasives.prerr_string

(* val prerr_int : int -> unit *)

let prerr_int = Pervasives.prerr_int

(* val prerr_float : float -> unit *)

let prerr_float = Dual.prerr_float

(* val prerr_endline : string -> unit *)

let prerr_endline = Pervasives.prerr_endline

(* val prerr_newline : unit -> unit *)

let prerr_newline = Pervasives.prerr_newline

(* val read_line : unit -> string *)

let read_line = Pervasives.read_line

(* val read_int : unit -> int *)

let read_int = Pervasives.read_int

(* val read_float : unit -> float *)

let read_float = Dual.read_float

type open_flag = Pervasives.open_flag

(* val open_out : string -> out_channel *)

let open_out = Pervasives.open_out

(* val open_out_bin : string -> out_channel *)

let open_out_bin = Pervasives.open_out_bin

(* val open_out_gen : open_flag list * int * string -> out_channel *)

let open_out_gen = Pervasives.open_out_gen

(* val flush : out_channel -> unit *)

let flush = Pervasives.flush

(* val flush_all : unit -> unit *)

let flush_all = Pervasives.flush_all

(* val output_char : out_channel * char -> unit *)

let output_char = Pervasives.output_char

(* val output_string : out_channel * string -> unit *)

let output_string = Pervasives.output_string

(* val output : out_channel * string * int * int -> unit *)

let output = Pervasives.output

(* val output_byte : out_channel * int -> unit *)

let output_byte = Pervasives.output_byte

(* val output_binary_int : out_channel * int -> unit *)

let output_binary_int = Pervasives.output_binary_int

(* val output_value : out_channel * 'a -> unit *)

let output_value = Pervasives.output_value

(* val seek_out : out_channel * int -> unit *)

let seek_out = Pervasives.seek_out

(* val pos_out : out_channel -> int *)

let pos_out = Pervasives.pos_out

(* val out_channel_length : out_channel -> int *)

let out_channel_length = Pervasives.out_channel_length

(* val close_out : out_channel -> unit *)

let close_out = Pervasives.close_out

(* val close_out_noerr : out_channel -> unit *)

let close_out_noerr = Pervasives.close_out_noerr

(* val set_binary_mode_out : out_channel * bool -> unit *)

let set_binary_mode_out = Pervasives.set_binary_mode_out

(* val open_in : string -> in_channel *)

let open_in = Pervasives.open_in

(* val open_in_bin : string -> in_channel *)

let open_in_bin = Pervasives.open_in_bin

(* val open_in_gen : open_flag list * int * string -> in_channel *)

let open_in_gen = Pervasives.open_in_gen

(* val input_char : in_channel -> char *)

let input_char = Pervasives.input_char

(* val input_line : in_channel -> string *)

let input_line = Pervasives.input_line

(* val input : in_channel * string * int * int -> int *)

let input = Pervasives.input

(* val really_input : in_channel * string * int * int -> unit *)

let really_input = Pervasives.really_input

(* val input_byte : in_channel -> int *)

let input_byte = Pervasives.input_byte

(* val input_binary_int : in_channel -> int *)

let input_binary_int = Pervasives.input_binary_int

(* val input_value : in_channel -> 'a *)

let input_value = Pervasives.input_value

(* val seek_in : in_channel * int -> unit *)

let seek_in = Pervasives.seek_in

(* val pos_in : in_channel -> int *)

let pos_in = Pervasives.pos_in

(* val in_channel_length : in_channel -> int *)

let in_channel_length = Pervasives.in_channel_length

(* val close_in : in_channel -> unit *)

let close_in = Pervasives.close_in

(* val close_in_noerr : in_channel -> unit *)

let close_in_noerr = Pervasives.close_in_noerr

(* val set_binary_mode_in : in_channel * bool -> unit *)

let set_binary_mode_in = Pervasives.set_binary_mode_in

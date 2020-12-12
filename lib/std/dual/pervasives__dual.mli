(* Dual numbers, used for automatic differentiation *)
(* Added by B. Caillaud <benoit.caillaud@inria.fr> *)

type float = Dual.t

(* the core module. taken from Ocaml *)
(* pour debugger set arguments -nopervasives -i lib/pervasives.lsi *)

val ( = ) : 'a -> 'a -> bool

val ( <> ) : 'a -> 'a -> bool

val ( < ) : 'a -> 'a -> bool

val ( > ) : 'a -> 'a -> bool

val ( <= ) : 'a -> 'a -> bool

val ( >= ) : 'a -> 'a -> bool

val compare : 'a -> 'a -> int

val min : 'a -> 'a -> 'a

val max : 'a -> 'a -> 'a

val ( == ) : 'a -> 'a -> bool

val ( != ) : 'a -> 'a -> bool

val not : bool -> bool

val ( && ) : bool -> bool -> bool

val ( & ) : bool -> bool -> bool

val ( || ) : bool -> bool -> bool

val ( or ) : bool -> bool -> bool

val ( ~- ) : int -> int

val succ : int -> int

val pred : int -> int

val ( + ) : int -> int -> int

val ( - ) : int -> int -> int

val ( * ) : int -> int -> int

val ( / ) : int -> int -> int

val ( mod ) : int -> int -> int

val abs : int -> int

val max_int : int

val min_int : int

val ( land ) : int -> int -> int

val ( lor ) : int -> int -> int

val ( lxor ) : int -> int -> int

val lnot : int -> int

val ( lsl ) : int -> int -> int

val ( lsr ) : int -> int -> int

val ( asr ) : int -> int -> int

val ( ~-. ) : float -> float

val ( +. ) : float -> float -> float

val ( -. ) : float -> float -> float

val ( *. ) : float -> float -> float

val ( /. ) : float -> float -> float

val ( ** ) : float -> float -> float

val sqrt : float -> float

val exp : float -> float

val log : float -> float

val log10 : float -> float

val cos : float -> float

val sin : float -> float

val tan : float -> float

val acos : float -> float

val asin : float -> float

val atan : float -> float

val atan2 : float -> float -> float

val cosh : float -> float

val sinh : float -> float

val tanh : float -> float

val ceil : float -> float

val floor : float -> float

val abs_float : float -> float

val mod_float : float -> float -> float

val frexp : float -> float * int

val ldexp : float -> int -> float

val modf : float -> float * float

val float : int -> float

val float_of_int : int -> float

val truncate : float -> int

val int_of_float : float -> int

val infinity : float

val neg_infinity : float

val nan : float

val max_float : float

val min_float : float

val epsilon_float : float

type fpclass = Pervasives.fpclass

val classify_float : float -> fpclass

val ( ^ ) : string -> string -> string

val int_of_char : char -> int

val char_of_int : int -> char

val ignore : 'a -> unit

val string_of_bool : bool -> string

val bool_of_string : string -> bool

val string_of_int : int -> string

val int_of_string : string -> int

val string_of_float : float -> string

val float_of_string : string -> float

val fst : 'a * 'b -> 'a

val snd : 'a * 'b -> 'b

type in_channel = Pervasives.in_channel
type out_channel = Pervasives.out_channel

val stdin : in_channel

val stdout : out_channel

val stderr : out_channel

val print_char : char -> unit

val print_string : string -> unit

val print_int : int -> unit

val print_float : float -> unit

val print_endline : string -> unit

val print_newline : unit -> unit

val prerr_char : char -> unit

val prerr_string : string -> unit

val prerr_int : int -> unit

val prerr_float : float -> unit

val prerr_endline : string -> unit

val prerr_newline : unit -> unit

val read_line : unit -> string

val read_int : unit -> int

val read_float : unit -> float

type open_flag = Pervasives.open_flag

val open_out : string -> out_channel

val open_out_bin : string -> out_channel

val open_out_gen : open_flag list -> int -> string -> out_channel

val flush : out_channel -> unit

val flush_all : unit -> unit

val output_char : out_channel -> char -> unit

val output_string : out_channel -> string -> unit

val output : out_channel -> string -> int -> int -> unit

val output_byte : out_channel -> int -> unit

val output_binary_int : out_channel -> int -> unit

val output_value : out_channel -> 'a -> unit

val seek_out : out_channel -> int -> unit

val pos_out : out_channel -> int

val out_channel_length : out_channel -> int

val close_out : out_channel -> unit

val close_out_noerr : out_channel -> unit

val set_binary_mode_out : out_channel -> bool -> unit

val open_in : string -> in_channel

val open_in_bin : string -> in_channel

val open_in_gen : open_flag list -> int -> string -> in_channel

val input_char : in_channel -> char

val input_line : in_channel -> string

val input : in_channel -> string -> int -> int -> int

val really_input : in_channel -> string -> int -> int -> unit

val input_byte : in_channel -> int

val input_binary_int : in_channel -> int

val input_value : in_channel -> 'a

val seek_in : in_channel -> int -> unit

val pos_in : in_channel -> int

val in_channel_length : in_channel -> int

val close_in : in_channel -> unit

val close_in_noerr : in_channel -> unit

val set_binary_mode_in : in_channel -> bool -> unit


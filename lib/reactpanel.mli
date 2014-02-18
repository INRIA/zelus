
val go :
     int              (* period *)
  -> (unit -> bool)   (* reaction function;
                         returns true to terminate simulation *)
  -> (unit -> unit)   (* reset function *)
  -> unit

(* Return a list that can be passed to Arg.parse to allow react panel parameters
 * to be set at the command line. *)
val args : (Arg.key * Arg.spec * Arg.doc) list


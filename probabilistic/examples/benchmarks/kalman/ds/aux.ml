open Infer_ds;;

(*
let read_val : unit -> (float * float) option =
    fun _ ->
    try
        Scanf.scanf "%f, %f\n" (fun t o -> Some (t, o))
    with End_of_file -> None
;;
*)

let read_val : unit ->  float * float =
    fun _ ->
        Scanf.scanf "%f, %f\n" (fun t o -> (t, o))
;;


let get_mean (type a) : (a, float) random_var -> float =
    fun r ->
        match (Infer_ds.get_conditional r).distr with
        | UDistr (MGaussian (mu, sigma)) -> mu
        | _ -> assert false (* error *)
;;

let get_memory : unit -> float =
    fun _ ->
        (*let st = Gc.stat () in
        float_of_int st.live_words*)
        0.0
;;

let get_time : unit -> float =
    fun _ ->
        (*Sys.time ()*) 0.0
;;

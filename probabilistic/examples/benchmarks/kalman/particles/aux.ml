(* open Infer_ds_nogc;; *)

let warmup = ref 0 ;;
let perf = ref false;;
let perf_step = ref false;;
let mem = ref false;;
let select_particle = ref None;;

Arg.parse[
    ("-w", Set_int warmup, "Numberof warmup iterations"); 
    ("-perf", Unit (fun _ -> perf := true), "Performance testing");
    ("-perf-step", Unit (fun _ -> perf_step := true), "Performance testing on a per step basis");
    ("-mem", Unit (fun _ -> mem := true), "Memory performance testing");
    ("-particles", Int (fun i -> select_particle := Some i), "Number of particles (single run)")
] (fun _ -> ()) "Kalman particles test harness";;

let parts = ref 
    begin match !select_particle with
    | Some i -> i
    | None -> 10
    end
;;

let particles _ =
    !parts
;;


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

(* let get_mean (type a) : (a, float) random_var -> float = *)
(*     fun r -> *)
(*         match r.state with *)
(*         | Marginalized (MGaussian (mu, sigma)) -> mu *)
(*         | _ -> assert false (\* error *\) *)
(* ;; *)

let random_init : unit -> unit =
    fun _ ->
        Random.self_init ()
;;

let collect_garbage : unit -> unit =
    fun _ -> (*Gc.full_major ()*)()
;;

let get_memory : unit -> float =
    fun _ ->
        (*let st = Gc.stat () in
        float_of_int st.live_words*)
        0.0
;;

let get_time : unit -> float =
    fun _ ->
        (*Sys.time ()*)0.0
;;

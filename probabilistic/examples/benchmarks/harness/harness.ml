module Config = struct

  let warmup = ref 1
  let accuracy = ref None
  let perf = ref None
  let perf_step = ref None
  let mem = ref None
  let mem_ideal = ref None
  let min_particles = ref 1
  let max_particles = ref 100
  let exp_seq_flag = ref false
  let pgf_format = ref false
  let mse_target = ref None
  let mse_mag = ref 0.5
  let increment = ref 1

  let select_particle = ref None
  let num_runs = ref 10
  let seed = ref None
  let upper_quantile = 0.9
  let lower_quantile = 0.1
  let middle_quantile = 0.5


  let args =
    Arg.align [
      ("-w", Set_int warmup,
       "n Number of warmup iterations");
      ("-num-runs", Set_int num_runs,
       "n Number of runs");
      ("-acc", String (fun file -> accuracy := Some file),
       "file Accuracy testing" );
      ("-perf", String (fun file -> perf := Some file),
       "file Performance testing");
      ("-perf-step", String (fun file -> perf_step := Some file),
       "file Performance testing on a per step basis");
      ("-mem-step", String (fun file -> mem := Some file),
       " Memory testing on a per step basis");
      ("-mem-ideal-step", String (fun file -> mem_ideal := Some file),
       " Memory testing on a per step basis with GC at each step");
      ("-particles", Int (fun i -> select_particle := Some i),
       "n Number of particles (single run)");
      ("-min-particles", Int (fun i -> min_particles := i),
       "n Lower bound of the particles interval");
      ("-max-particles", Int (fun i -> max_particles := i),
       "n Upper bound of the particles interval");
      ("-exp", Set exp_seq_flag,
       " Exponentioal sequence");
      ("-pgf",  Set pgf_format,
       "PGF Format");
      ("-mse-target", Float (fun f -> mse_target := Some f),
       "n MSE Target value");
      ("-mse-mag", Float (fun f -> mse_mag := f),
       "n Magnitude compared to the MSE Target (log scale)");
      ("-incr", Int (fun i -> increment := i),
       "n Increment in the particles interval");
      ("-seed", Int (fun i -> seed := Some i),
       "n Set seed of random number generator");
    ]

  let () =
    Arg.parse args (fun _ -> ()) "particles test harness"

  let () =
    begin match !seed with
      | None -> Random.self_init()
      | Some i -> Random.init i
    end

  let () =
    begin match !select_particle with
      | Some i -> min_particles := i; max_particles := i
      | None -> ()
    end

  let parts = ref !min_particles

  let particles _ =
    !parts

  let () =
    if !accuracy = None && !perf = None &&
       !mem = None && !mem_ideal = None && !perf_step = None then begin
      Arg.usage args
        "No tests performed: -acc, -perf, -perf-step, -mem-step, or -mem-ideal-step required";
      exit 1
    end

end

let option_iter f o =
  begin match o with
    | Some x -> f x
    | None -> ()
  end

let array_flatten arr =
  let l1 = Array.length arr in
  let l2 = Array.length arr.(0) in
  let res = Array.make (l1 * l2) arr.(0).(0) in
  let k = ref 0 in
  for i = 0 to l1 - 1 do
    for j = 0 to l2 - 1 do
      res.(!k) <- arr.(i).(j);
      incr k;
    done
  done;
  res

let array_transpose arr =
  let l1 = Array.length arr in
  let l2 = Array.length arr.(0) in
  Array.init l2
    (fun i ->
       Array.init l1
         (fun j ->
            arr.(j).(i)))

let array_assoc x a =
  let res = ref None in
  Array.iter
    (fun (y, v) -> if x = y then res := Some v)
    a;
  begin match !res with
    | None -> raise Not_found
    | Some v -> v
  end

module Make(M: sig
    type input
    type output
    val read_input : unit -> input
    val main : int -> (input, output * float) Ztypes.cnode
  end) = struct
  open Ztypes

  let get_step () =
    let Cnode {alloc; reset; step; copy = _} = M.main (Config.particles ()) in
    let state = alloc () in
    reset state;
    fun i -> step state i

  let rec read_file _ =
    try
      let s = M.read_input () in
      s :: read_file ()
    with End_of_file -> []

  let gc_stat () =
    begin match !Config.mem, !Config.mem_ideal with
      | Some _, None ->
          let st = Gc.stat () in
          let words = float_of_int (st.live_words) in
          words /. 1000.
      | None, Some _ ->
          let () = Gc.compact () in
          let st = Gc.stat () in
          let words = float_of_int (st.live_words) in
          words /. 1000.
      | None, None -> 0.
      | Some _, Some _ -> assert false
    end

  let stats arr =
    (* Format.printf "XXXXXX "; *)
    (* let carr = Array.copy arr in *)
    (* (\* Array.sort compare carr; *\) *)
    (* Array.iter (fun x -> Format.printf "%f, " x) carr; *)
    (* Format.printf "XXXXXX@."; *)

    let len_i = Array.length arr in
    let len = float_of_int len_i in
    Array.sort compare arr;
    let upper_idx = min (len_i - 1) (truncate (len *. Config.upper_quantile +. 0.5)) in
    let lower_idx = min (len_i - 1) (truncate (len *. Config.lower_quantile +. 0.5)) in
    let middle_idx = min (len_i - 1) (truncate (len *. Config.middle_quantile +. 0.5)) in
    (Array.get arr lower_idx, Array.get arr middle_idx, Array.get arr upper_idx)

  let stats_per_particles x_runs_particles =
    Array.map
      (fun (particles, runs) ->
         (particles, stats (array_flatten runs)))
      x_runs_particles

  let stats_per_step x_runs_particles =
    Array.map
      (fun (particles, runs) ->
         let steps = array_transpose runs in
         (particles, Array.map (fun a -> stats a) steps))
      x_runs_particles


  let do_warmup n inp =
    let step = get_step () in
    Gc.compact ();
    for _ = 1 to n do
      List.iter
        (fun i ->
           let _, _ = step i in
           ())
        inp
    done

  let run inp =
    let step = get_step () in
    let len = List.length inp in
    let times = Array.make len 0. in
    let mems = Array.make len 0. in
    let final_mse = ref 0. in
    List.iteri
      (fun idx i ->
         let time_pre = Sys.time () in
         let _, mse = step i in
         let time = Sys.time () -. time_pre in
         times.(idx) <- time *. 1000.;
         mems.(idx) <- gc_stat();
         final_mse := mse)
      inp;
    (!final_mse, times, mems)

  let do_runs num_runs inp =
    let mse_runs = Array.make num_runs 0.0 in
    let times_runs = Array.make num_runs [||] in
    let mems_runs = Array.make num_runs [||] in
    for idx = 0 to num_runs - 1 do
      let mse, times, mems = run inp in
      Format.printf ".@?";
      mse_runs.(idx) <- mse;
      times_runs.(idx) <- times;
      mems_runs.(idx) <- mems
    done;
    Format.printf "@.";
    mse_runs, times_runs, mems_runs

  type search_kind = Exp | Linear

  let search_particles_target mse_target mag num_runs inp =
    let rec search k p incr =
      Format.printf "Trying %d particles@?" p;
      Config.parts := p;
      let mse_runs, _, _ = (do_runs num_runs inp) in
      let _, _, mse_max = stats mse_runs in
      let r = abs_float (log10 mse_max -. log10 mse_target) in
      begin match k with
        | Exp when r > mag ->
            if (10 * p < 10000)
            then search Exp (10 * p) p
            else search Linear (2 * p) p
        | Exp when r <= mag -> search Linear incr incr
        | Linear when r > mag -> search Linear (p + incr) incr
        | Linear when r <= mag -> p
        | _ -> assert false
      end
    in
    search Exp 1 1

  let do_runs_particles particles_list num_runs inp =
    let len = List.length particles_list in
    let mse_runs_particles = Array.make len (0, [||]) in
    let times_runs_particles = Array.make len (0, [||]) in
    let mems_runs_particles = Array.make len (0, [||]) in
    List.iteri
      (fun idx particles ->
         Format.printf "%d: start %d runs (+%d warmups) for %d particles@?"
           idx num_runs !Config.warmup particles;
         Config.parts := particles;
         do_warmup !Config.warmup inp;
         let mse_runs, times_runs, mems_runs = do_runs num_runs inp in
         mse_runs_particles.(idx) <- (particles, mse_runs);
         times_runs_particles.(idx) <- (particles, times_runs);
         mems_runs_particles.(idx) <- (particles, mems_runs);
         let _, mse_mean, _ = stats (Array.copy mse_runs) in
         let _, time_mean, _ = stats (array_flatten times_runs) in
         Format.printf "Means: accuracy = %f, times = %f@."
           mse_mean time_mean)
      particles_list;
    mse_runs_particles, times_runs_particles, mems_runs_particles

  let output_stats_per_particles file value stats  =
    let ch = open_out file in
    let fmt = Format.formatter_of_out_channel ch in
    Format.fprintf fmt
      "number of particles, %s lower quantile (%f), median, upper quantile (%f)@."
      value Config.lower_quantile Config.upper_quantile;
    if not !Config.pgf_format then begin
      Array.iter
        (fun (particles, (low, mid, high)) ->
           Format.fprintf fmt "%d, %f, %f, %f@." particles low mid high)
        stats;
    end
    else begin
      Array.iter
        (fun (particles, (low, mid, high)) ->
           Format.fprintf fmt "%d   %f   %f   %f@." particles mid (mid -. low) (high -. mid))
        stats;
    end;
    close_out ch

  let output_stats_per_step file particles value stats =
    let ch = open_out file in
    let fmt = Format.formatter_of_out_channel ch in
    Format.fprintf fmt
      "step (%d particles), %s lower quantile (%f), median, upper quantile (%f)@."
      particles value Config.lower_quantile Config.upper_quantile;
    if not !Config.pgf_format then begin
      Array.iteri
        (fun idx (low, mid, high) ->
           Format.fprintf fmt "%d, %f, %f, %f@." idx low mid high)
        stats;
    end
    else begin
      Array.iteri
        (fun idx (low, mid, high) ->
           Format.fprintf fmt "%d   %f   %f   %f@." idx mid (mid -. low) (high -. mid))
        stats;
    end;
    close_out ch

  let output_perf file times_runs_particles =
    let stats = stats_per_particles times_runs_particles in
    output_stats_per_particles file "time in ms" stats

  let output_accuracy file mse_runs_particles =
    let stats =
      Array.map
        (fun (particles, runs) -> (particles, stats runs))
        mse_runs_particles
    in
    output_stats_per_particles file "mse" stats

  let output_perf_step file times_runs_particles =
    let stats = stats_per_step times_runs_particles in
    output_stats_per_step file !Config.parts "time in ms" (array_assoc !Config.parts stats)

  let output_mem file mems_runs_particles =
    let stats = stats_per_step mems_runs_particles in
    output_stats_per_step file !Config.parts "thousands live heap words" (array_assoc !Config.parts stats)

  let rec seq min incr max =
    if min > max then []
    else
      min :: seq (min + incr) incr max

  let exp_seq =
    let rec seq p incr exp  max =
      if p > max then []
      else
        p ::
        if p >= exp then seq (p + (exp / 2)) (exp / 2) (10 * exp) max
        else seq (p + incr) incr exp max
    in
    seq 1 1 10

  let run () =
    let inp = read_file () in
    let num_runs = !Config.num_runs in
    let particles_list =
      begin match !Config.mse_target, !Config.exp_seq_flag with
        | Some mt, false ->
            [search_particles_target mt !Config.mse_mag num_runs inp]
        | None, false ->
            seq !Config.min_particles !Config.increment !Config.max_particles
        | None, true ->
            exp_seq !Config.max_particles
        | Some _, true ->
            Arg.usage Config.args
              "options -exp and -mse-target cannot be used simultaneously";
            exit 1

      end
    in
    let mse_runs_particles, times_runs_particles, mems_runs_particles =
      do_runs_particles particles_list !Config.num_runs inp
    in
    option_iter
      (fun file -> output_accuracy file mse_runs_particles) !Config.accuracy;
    option_iter
      (fun file -> output_perf file times_runs_particles) !Config.perf;
    option_iter
      (fun file -> output_perf_step file times_runs_particles) !Config.perf_step;
    option_iter
      (fun file -> output_mem file mems_runs_particles) !Config.mem;
    option_iter
      (fun file -> output_mem file mems_runs_particles) !Config.mem_ideal

end

open Stats
open Probzelus

module Make(M: sig
    type input
    type output
    val read_input : unit -> input
    val main : int -> (input, output) Ztypes.cnode
    val metrics : int -> ((input * output), float) Ztypes.cnode
  end) = struct

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

  open Ztypes

  let get_step () =
    let Cnode {alloc; reset; step; copy = _} = M.main (Config.particles ()) in
    let state = alloc () in
    reset state;
    fun i -> step state i

  let get_step_metrics () =
    let Cnode {alloc; reset; step; copy = _} = M.metrics (Config.particles ()) in
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

  let stats = Stats.stats (Config.lower_quantile,
                           Config.middle_quantile,
                           Config.upper_quantile)

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
           let _ = step i in
           ())
        inp
    done

  let run inp =
    let step = get_step () in
    let step_metrics = get_step_metrics () in
    let len = List.length inp in
    let times = Array.make len 0. in
    let mems = Array.make len 0. in
    let final_mse = ref 0. in
    List.iteri
      (fun idx i ->
         let has_sample = ref false in
         while not !has_sample do
           let time_pre = Sys.time () in
           let out = step i in
           let time = Sys.time () -. time_pre in
           try
             let mse = step_metrics (i, out) in
             times.(idx) <- time *. 1000.;
             mems.(idx) <- gc_stat();
             final_mse := mse;
             has_sample := true
           with Distribution.Draw_error -> 
             times.(idx) <- times.(idx) +. (time *. 1000.);
             print_string "x"
         done)
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
            if (10 * p < 100000)
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

  let output_stats_per_particles file value_label stats  =
    output_stats !Config.pgf_format file "number of particles" value_label stats

  let output_stats_per_step file particles value_label stats =
    let idx_label = "step ("^(string_of_int particles)^" particules)" in
    let stats =
      Array.mapi (fun i (low, mid, high) -> (i, (low, mid, high))) stats
    in
    output_stats !Config.pgf_format file idx_label value_label stats

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
    output_stats_per_step file !Config.parts
      "time in ms" (array_assoc !Config.parts stats)

  let output_mem file mems_runs_particles =
    let stats = stats_per_step mems_runs_particles in
    output_stats_per_step file !Config.parts
      "thousands live heap words" (array_assoc !Config.parts stats)

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

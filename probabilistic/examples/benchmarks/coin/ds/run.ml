
let get_step () =
  let Node{alloc; reset; step} = Coin_ds.main (Aux.particles ()) in
  let state = alloc () in
  reset state;
  fun i -> step state i

let rec read_file _ =
  try
    let s = Scanf.scanf ("%f, %B\n") (fun t o -> (t, o)) in
    s :: read_file ()
  with End_of_file -> []

let run inp res =
  let step = get_step () in
  Random.self_init ();
  List.iteri
    (fun idx i ->
       let time_pre = Sys.time () in
       let ret, mse = step i in
       let time = Sys.time () -. time_pre in
       Array.set res idx ((string_of_float mse) ^ ", " ^ (string_of_float (time *. 1000.)) ^ "\n"))
    inp

let runmem inp =
  let step = get_step () in
  List.iteri
    (fun idx i ->
       let node, mse = step i in
       Gc.full_major ();
       let st = Gc.stat () in
       let major_words = float_of_int (st.live_words) in
       let space = major_words /. 1000. in
       Format.printf "%f, %f@." mse space)
    inp

let runacc inp =
  let step = get_step () in
  let ret = ref 0. in
  Random.self_init ();
  List.iteri
    (fun idx i ->
       let n, mse = step i in
       ret := mse)
    inp;
  !ret

let runperf inp res idx_init =
  let step = get_step () in
  Random.self_init ();
  List.iteri
    (fun idx i ->
       let time_pre = Sys.time () in
       let _ = step i in
       let time = Sys.time () -. time_pre in
       Array.set res (idx_init + idx) (time *. 1000.))
    inp

let stats arr =
  let upper_quantile = 0.9 in
  let lower_quantile = 0.1 in
  let middle_quantile = 0.5 in
  let len = float_of_int (Array.length arr) in
  Array.sort compare arr;
  let upper_idx = truncate (len *. upper_quantile +. 0.5) in
  let lower_idx = truncate (len *. lower_quantile +. 0.5) in
  let middle_idx = truncate (len *. middle_quantile +. 0.5) in
  (Array.get arr lower_idx, Array.get arr middle_idx, Array.get arr upper_idx)

let do_runacc inp =
  let num_runs = 100 in
  let ret : float array =
    Array.init num_runs (fun idx -> runacc inp)
  in
  stats ret

let do_runperf inp =
  let steps = List.length inp in
  let num_runs = 100 in
  let len = steps * num_runs in
  let ret : float array = Array.make len 0.0 in
  for idx = 0 to num_runs - 1 do
    runperf inp ret (idx * steps)
  done;
  stats ret

let do_runperf_step inp =
  let steps = List.length inp in
  let num_runs = 100 in
  let len = steps * num_runs in
  let ret : float array = Array.make len 0.0 in
  for idx = 0 to num_runs - 1 do
    runperf inp ret (idx * steps)
  done;
  let agg : (float * float * float) array =
    Array.init steps
      (fun step ->
         let tmp : float array =
           Array.init num_runs (fun run -> Array.get ret (run * steps + step))
         in
         stats tmp)
  in
  agg


let rec do_runs n inp ret =
  for i = 1 to n do
    run inp ret
  done

let main =
  let inp = read_file () in
  let tmp : string array = Array.make (List.length inp) ("") in
  do_runs !Aux.warmup inp tmp;

  begin match !Aux.select_particle with
  | Some p ->
      if !Aux.perf_step then (
        Format.printf "Performance Testing on a per step basis@.";
        Array.iteri (fun i (low, mid, high) ->
            Format.printf "%i, %f, %f, %f@." i mid low high)
          (do_runperf_step inp)
      ) else (
        if !Aux.mem then (
          runmem inp;
          do_runs 1 inp tmp;
        ) else (
          let ret : string array = Array.make (List.length inp) ("") in
          let tmp : string array = Array.make (List.length inp) ("") in
          run inp ret;
          do_runs 1 inp tmp;
          Format.printf "%s@." (String.concat "" (Array.to_list ret))
        )
      )
  | None ->
      if !Aux.perf then (
        Format.printf "Performance Testing@.";
        let min_particles = 1 in
        let max_particles = 50 in
        for i = min_particles to max_particles do
          Aux.parts := i;
          let (low, mid, high) = do_runperf inp in
          do_runs 1 inp tmp;
          Format.printf "%d, %f, %f, %f@." i low mid high;
        done
      )
      else (
        print_string "Accuracy Testing\n";
        flush stdout;

        let min_particles = 1 in
        let max_particles = 100 in
        for i = min_particles to max_particles do
          Aux.parts := i;
          let low, mid, high = do_runacc inp in
          do_runs 1 inp tmp;
          Format.printf "%d, %f, %f, %f@." i mid low high;
        done
      )
  end

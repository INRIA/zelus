let rec read_file _ =
    try 
        let s = Scanf.scanf ("%f, %f\n") (fun t o -> (t, o)) in
        s :: read_file ()
    with End_of_file -> []
in

let run inp res =
    let Node{alloc; reset; step} = Kalman_particles.main () in
    let state = alloc () in
    reset state;
    Random.self_init ();
    let iref = ref inp in
    let idx = ref 0 in

    while not (!iref = []) do
        match !iref with
        | [] -> assert false
        | i :: rest ->
            let time_pre = Sys.time () in
            let st = step state i in
            let time = Sys.time () -. time_pre in
            iref := rest;
            Array.set res !idx (st ^ ", " ^ (string_of_float time) ^ "\n");
            idx := ((!idx) + 1);
            Gc.full_major ();
    done
in

let runperf inp res idx =
    let Node{alloc; reset; step} = Kalman_particles.main () in
    let state = alloc () in
    reset state;
    Random.self_init ();
    let iref = ref inp in

    while not (!iref = []) do
        match !iref with
        | [] -> assert false
        | i :: rest ->
            let time_pre = Sys.time () in
            let st = step state i in
            let time = Sys.time () -. time_pre in
            iref := rest;
            Array.set res !idx time;
            idx := ((!idx) + 1);
            Gc.full_major ();
    done
in

let stats arr =
    let upper_quantile = 0.9 in
    let lower_quantile = 0.1 in
    let middle_quantile = 0.5 in

    Array.sort compare arr;

    let upper_idx = truncate ((float_of_int (Array.length arr)) *. upper_quantile +. 0.5) in
    let lower_idx = truncate ((float_of_int (Array.length arr)) *. lower_quantile +. 0.5) in
    let middle_idx = truncate ((float_of_int (Array.length arr)) *. middle_quantile +. 0.5) in

    (Array.get arr lower_idx, Array.get arr middle_idx, Array.get arr upper_idx)
in

let do_runperf inp =
    let steps = List.length inp in
    let num_runs = 50 in
    let len = (steps * num_runs) in

    let ret : float array = Array.make len 0.0 in
    let idx = ref 0 in
    while not (!idx = len) do
        runperf inp ret idx
    done;
    assert (!idx = len);
    stats ret
in

let rec do_runs n inp ret =
    if n = 0 then ()
    else (
        run inp ret;
        do_runs (n - 1) inp ret
    )
in

let inp = read_file () in
if !Aux.perf then
    (
        let tmp : string array = Array.make (List.length inp) ("") in
        do_runs !Aux.warmup inp tmp;

        let min_particles = 1 in
        let max_particles = 50 in
        let rec perftest i =
            if (i = max_particles) then () else
                Aux.parts := i;

                let (low, mid, high) = do_runperf inp in
                do_runs 1 inp tmp;
                print_string ((string_of_int i) ^ ", " ^ (string_of_float low) ^ ", " ^ (string_of_float mid) ^ ", " ^ (string_of_float high) ^ "\n");
                flush stdout;
                perftest (i+1)
        in
        perftest min_particles 
    )
else
    assert false (* TODO *)



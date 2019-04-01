let warmup = ref 0 in
Arg.parse [("-w", Set_int warmup, "Numberof warmup iterations")] (fun _ -> ()) "";

let rec read_file _ =
    try 
        let s = Scanf.scanf ("%f, %f\n") (fun t o -> (t, o)) in
        s :: read_file ()
    with End_of_file -> []
in

let run inp res =
    let Node{alloc; reset; step} = Kalman_ds_nogc.main in
    let state = alloc () in
    reset state;
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

let rec do_runs n inp ret =
    if n = 0 then ()
    else (
        run inp ret;
        do_runs (n - 1) inp ret
    )
in


let inp = read_file () in
let ret : string array = Array.make (List.length inp) ("") in
let tmp : string array = Array.make (List.length inp) ("") in
do_runs !warmup inp ret;
run inp ret;
do_runs 1 inp tmp;
print_string (String.concat "" (Array.to_list ret))

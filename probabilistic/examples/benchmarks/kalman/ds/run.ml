let warmup = ref 0 in
Arg.parse [("-w", Set_int warmup, "Numberof warmup iterations")] (fun _ -> ()) "";

let rec read_file _ =
    try 
        let s = Scanf.scanf ("%f, %f\n") (fun t o -> (t, o)) in
        s :: read_file ()
    with End_of_file -> []
in

let run inp =
    let Node{alloc; reset; step} = Kalman_ds.main in
    let state = alloc () in
    reset state;
    let iref = ref inp in
    let resref = ref "" in

    while not (!iref = []) do
        match !iref with
        | [] -> assert false
        | i :: rest ->
            let st = step state i in
            resref := !resref ^ st;
            iref := rest
    done;
    !resref
in

let rec do_runs n inp =
    if n = 0 then ()
    else (
        run inp;
        print_string ("Warmup " ^ (string_of_int n));
        do_runs (n - 1) inp
    )
in


let inp = read_file () in
print_string "Starting Warmup";
do_runs !warmup inp;
let res = run inp in
do_runs 1 inp;
print_string res

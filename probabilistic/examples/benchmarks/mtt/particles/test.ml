open Owl;;
open Ztypes;;
open Mttlib;;

let data_file = ref "" ;;
Arg.parse [("-f", Set_string data_file, "")] (fun _ -> ()) "";;
let chan = Scanf.Scanning.open_in !data_file

let read_input () =
  let mk_vec a b =
      Mat.of_arrays [| [| a |];
                       [| b |] |]
  in
  let process_vec_list _ = 
    let rec process_list_helper fst =
      try
        Scanf.bscanf chan "]" (fun _ -> ()) 0;
        []
      with Scanf.Scan_failure _ ->
        let this_elem = if fst then
          Scanf.bscanf chan "(%f, %f)" (fun x y -> mk_vec x y) 
        else 
          Scanf.bscanf chan ",(%f, %f)" (fun x y -> mk_vec x y) 
        in
        this_elem :: (process_list_helper false)
    in
    Scanf.bscanf chan "[" (fun _ -> ()) 0;
    process_list_helper true
  in

  let process_tr_list _ = 
    let rec process_list_helper fst =
      try
        Scanf.bscanf chan "]" (fun _ -> ()) 0;
        []
      with Scanf.Scan_failure _ ->
        let this_elem = if fst then
          Scanf.bscanf chan "(%i, %f, %f)" (fun i x y -> (i, mk_vec x y))
        else 
          Scanf.bscanf chan ",(%i, %f, %f)" (fun i x y -> (i, mk_vec x y))
        in
        this_elem :: (process_list_helper false)
    in
    Scanf.bscanf chan "[" (fun _ -> ()) 0;
    process_list_helper true
  in


  let truth = process_tr_list () in
  Scanf.bscanf chan " : " (fun _ -> ()) 0;
  let obs = process_vec_list () in

  Scanf.bscanf chan "\n" (fun _ -> ()) 0;
  (truth, obs)

let run () = 
    let Cnode {alloc; reset; step; copy = _} = Mtt_particles.main 1000 in
    let state = alloc () in
    reset state;
    let rec do_run () =
        try 
            let (tr, obs) = read_input () in
            let (_, err) = step state (tr, obs) in
            print_string (string_of_float err ^ "\n");
            do_run ()
        with End_of_file -> ()
    in
    do_run ()
;;

run ()


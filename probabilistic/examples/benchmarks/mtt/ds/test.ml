open Owl;;
open Ztypes;;
open Mttlib;;

let read_input () =
  let mk_vec a b =
      Mat.of_arrays [| [| a |];
                       [| b |] |]
  in
  let process_vec_list _ = 
    let rec process_list_helper fst =
      try
        Scanf.scanf "]" (fun _ -> ()) 0;
        []
      with Scanf.Scan_failure _ ->
        let this_elem = if fst then
          Scanf.scanf "(%f, %f)" (fun x y -> mk_vec x y) 
        else 
          Scanf.scanf ",(%f, %f)" (fun x y -> mk_vec x y) 
        in
        this_elem :: (process_list_helper false)
    in
    Scanf.scanf "[" (fun _ -> ()) 0;
    process_list_helper true
  in

  let process_tr_list _ = 
    let rec process_list_helper fst =
      try
        Scanf.scanf "]" (fun _ -> ()) 0;
        []
      with Scanf.Scan_failure _ ->
        let this_elem = if fst then
          Scanf.scanf "(%i, %f, %f)" (fun _ x y -> mk_vec x y) 
        else 
          Scanf.scanf ",(%i, %f, %f)" (fun _ x y -> mk_vec x y) 
        in
        this_elem :: (process_list_helper false)
    in
    Scanf.scanf "[" (fun _ -> ()) 0;
    process_list_helper true
  in


  let truth = process_tr_list () in
  Scanf.scanf " : " (fun _ -> ()) 0;
  let obs = process_vec_list () in

  Scanf.scanf "\n" (fun _ -> ()) 0;
  (truth, obs)

let run () = 
    let Cnode {alloc; reset; step; copy = _} = Mtt_ds.main 1000 in
    let state = alloc () in
    reset state;
    let rec do_run () =
        try 
            let (tr, obs) = read_input () in
            let (v, _) = step state (tr, obs) in
            print_string (Util.string_of_vec2_list v ^ "\n");
            do_run ()
        with End_of_file -> ()
    in
    do_run ()
;;

run ()


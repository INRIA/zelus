(* simulation (any) function *)
let main x = Sandbox.main x;;
(* (discrete) simulation loop *)
while true do main () done;
exit(0);;

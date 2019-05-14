open Infer_ds;;

let init_pstate _ : Infer.pstate =
    {
        idx = 0;
        scores = Array.make 1 0.0;
    }
;;

let model prob =
    let x0 = assume_constant "x0" (mgaussian 0.0 1.0) in
    let x1 = assume_conditional "x1" x0 (affine_mean_gaussian 1.0 0.0 1.0) in
    obs prob 1.0 x1;
    print_state x0;
    let x2 = assume_conditional "x2" x0 (affine_mean_gaussian 1.0 0.0 1.0) in
    let x3 = assume_conditional "x3" x2 (affine_mean_gaussian 1.0 0.0 1.0) in
    obs prob 1.0 x3;
    x2;;

let ret = model (init_pstate ());;
Gc.full_major ();;
print_state ret;;

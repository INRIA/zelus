open Owl
open Owl_plplot

let pca ?(n_components=2) train =
  let x = Mat.(train - (mean ~axis:0 train)) in
  let u,s,v = Linalg.D.svd x in
  let k = n_components - 1 in
  let v = Mat.(v.${[[]; [0; k]]}) in
  fun test -> Mat.(test *@ v)

let split_data ~p m = 
  let extract_labels m = 
    Mat.(m.${[[]; [0;-2]]}),
    Mat.(m.${[[]; [-1]]} -$ 1.)
  in
  let n, _ = Mat.shape m in
  let tflag = Mat.bernoulli ~p:0.7 n 1 in
  let train_idx = Mat.filter ((=) 1.) tflag in
  let test_tidx = Mat.filter ((=) 0.) tflag in
  extract_labels (Mat.rows m train_idx),
  extract_labels (Mat.rows m test_tidx)

let score train =
  let mu = Mat.mean ~axis:0 train in
  let sigma = Mat.std ~axis:0 train in
  fun x -> 
    let lpdf = 
      Mat.mapi_2d 
        (fun i j v -> 
           Stats.gaussian_logpdf 
             v 
             ~mu:(Mat.get mu 0 j) 
             ~sigma:(Mat.get sigma 0 j)) 
        x
    in
    Mat.sum ~axis:1 lpdf;;

let classifier train_data train_label =
  let n, _ = Mat.shape train_data in
  let gidx = Mat.filter ((=) 1.) train_label in
  let bidx = Mat.filter ((=) 0.) train_label in
  let gdata = Mat.rows train_data gidx in
  let bdata = Mat.rows train_data bidx in
  let glp = float (Array.length gidx) /. (float n) in
  let blp = float (Array.length bidx) /. (float n) in
  let gscore = score gdata in
  let bscore = score bdata in
  fun test_data -> 
    let sg = gscore test_data in
    let sb = bscore test_data in
    Mat.(sg +$ glp >. sb +$ blp);;

let accuracy k test_data test_label = 
  let pred = k test_data in
  let s = Mat.sum ~axis:0 Mat.(pred =. test_label) in
  let n, _ = Mat.shape pred in
  (Mat.get s 0 0) /. (float n)

let run m = 
  let (train_data, train_label), (test_data, test_label) = split_data ~p:0.75 m in
  (* Transformers *)
  let mpca   = pca ~n_components:2 train_data in
  let gender = fun x -> Mat.col x 8 in
  (* Classifiers *)
  let k_simple = classifier train_data train_label in
  let k_pca    = classifier (mpca train_data) train_label in
  let k_dummy  = classifier (gender train_data) train_label in
  (* Accuracies *)
  let acc_simple = accuracy k_simple test_data test_label in
  let acc_pca    = accuracy k_pca (mpca test_data) test_label in
  let acc_dummy  = accuracy k_dummy (gender test_data) test_label in
  (* Results *)
  Mat.of_array [|acc_simple; acc_pca; acc_dummy|] 1 3

let _ = 
  let m = Mat.load_txt ~sep:" " "german.data-numeric" in
  let rec exec n acc = 
    match n with
    | 0 -> acc
    | _ -> exec (n-1) Mat.(acc @= run m)
  in
  let acc = exec 100 (run m) in
  Mat.print (Mat.mean ~axis:0 acc)

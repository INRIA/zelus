type pstate = Infer.pstate

type 'a random =
    | LLRand : ('a, 'b) Infer_ds.random_var -> 'b random
    | Delta of 'a

let value (type a) : (pstate * a random) -> a =
    fun (prob, var) ->
    match var with
    | Delta x -> x
    | LLRand rvar ->
        Infer_ds.get_value rvar
;;

let draw (type a) : a random -> a =
    fun var ->
        match var with
        | Delta x -> x
        | LLRand rvar -> Infer_ds.draw rvar

let delta (type a) : pstate * a -> a random =
    fun (_,x) -> Delta x
;;

let print_var a =
    match a with
    | Delta x -> Format.printf "%f\n" x
    | LLRand rvar -> Infer_ds.print_state rvar
;;

let rec assume (type a) (type b):
    (pstate * (a, b) Distribution_ds.dist * a random) -> b random =
    fun (prob, dist, parent) ->
    let llvar : (a, b) Infer_ds.random_var = 
        begin match parent with
        (* If our input is a delta, convert conditioned distributions to unconditioned distributions *)
        | Delta x -> 
            begin match dist with
                | CDist (AffineMeanGaussian (1.0, 0.0, variance)) ->
                    Infer_ds.assume_constant "node" (Infer_ds.MGaussian (x, variance))
                | CDist (AffineMeanGaussian (_, _, _)) -> assert false
                | CDist (CBernoulli) -> Infer_ds.assume_constant "node" (MBernoulli x)
                | UDist d -> Infer_ds.assume_constant "node" d
            end
        (* Otherwise, call the appropriate low-level initialization to add a new node to the graph *)
        | LLRand rvar -> 
            begin match (dist, rvar.distr) with
                | (Distribution_ds.CDist (AffineMeanGaussian (slope,b,variance)), 
                   CDistr (_, AffineMeanGaussian (_,_,_))) ->
                    Infer_ds.assume_conditional "node" rvar (AffineMeanGaussian (slope,b,variance))
                | (Distribution_ds.CDist (AffineMeanGaussian (slope,b,variance)), 
                   UDistr (MGaussian(_,_))) ->
                    Infer_ds.assume_conditional "node" rvar (AffineMeanGaussian (slope,b,variance))
                | (Distribution_ds.UDist d, _) -> Infer_ds.assume_constant "node" d
                | _ ->
                    (* If we don't recognize the conjugacy of the distributions, force a sample *)
                    (* TODO: Not very DRY *)
                    let x = Infer_ds.get_value rvar in
                    begin match dist with
                        | CDist (AffineMeanGaussian (1.0, 0.0, variance)) ->
                            Infer_ds.assume_constant "node" (Infer_ds.MGaussian (x, variance))
                        | CDist (AffineMeanGaussian (_, _, _)) -> assert false
                        | CDist (CBernoulli) -> Infer_ds.assume_constant "node" (MBernoulli x)
                        | UDist d -> Infer_ds.assume_constant "node" d
                    end
            end
        end
    in
    LLRand llvar;;

let observe (type a) : (pstate * (a random) * a) -> unit =
    fun (prob, obs_variable, obs_value) ->
        match obs_variable with
        | Delta x -> assert false
        | LLRand rvar -> Infer_ds.obs prob obs_value rvar
;;


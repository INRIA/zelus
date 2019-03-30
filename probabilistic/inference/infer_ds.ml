(** Inference with delayed sampling *)
open Ztypes

type pstate = {
    idx : int;
    scores : float array;
};;

type 'a infer_state = {
    states : 'a array;
    scores : float array;
};;

let infer n (Node {alloc; reset; step}) =
    let normalize scores =
        let logsumexp s =
            let maxs = Array.fold_right max s neg_infinity in
            let exps = Array.map (fun si -> exp (si -. maxs)) s in
            let sumexps = Array.fold_right (fun a b -> a +. b) exps 0.0 in
            maxs +. (log sumexps)
        in
        let norm_const = logsumexp scores in
        Array.iteri (fun i s -> Array.set scores i (s -. norm_const)) scores
    in

    let ret = Node {
        alloc = begin fun () -> 
            {
                states = Array.init n (fun _ -> alloc ());
                scores = Array.make n 0.0;
            }
        end;
        reset = begin fun s -> 
            Array.iter reset s.states;
            Array.fill s.scores 0 n 0.0;
        end;
        step = (fun s (c, input) -> 
            let new_state = {
                states = Array.mapi (fun i state ->
                    step state ({idx = i; scores = s.scores;}, input)
                ) s.states;
                scores = s.scores;
            } in
            normalize new_state.scores;
            Gc.full_major ();
            Distribution.Dist_support (List.mapi (fun i s ->
                (Array.get new_state.states i, s)
            ) (Array.to_list new_state.scores))
        )
    } in
    ret
;;

let factor ((prob : pstate), s) =
    let cur_score = Array.get prob.scores prob.idx in
    Array.set prob.scores prob.idx (cur_score +. s)
;;

type mgaussiant = float
type mbetat = float
type mbernoullit = bool
type 'a mtype = 'a

(** Marginalized distribution *)
type 'a mdistr =
  | MGaussian : float * float -> mgaussiant mdistr
  | MBeta : float * float -> mbetat mdistr
  | MBernoulli : float -> bool mdistr

(** Conditionned distribution *)
type ('m1, 'm2) cdistr =
  | AffineMeanGaussian: float * float * float -> (mgaussiant, mgaussiant) cdistr
  | CBernoulli : (mbetat, mbernoullit) cdistr

(** Random variable *)
type ('a, 'b) random_var =
  { name : string;
    mutable children : 'b rv_from Weak.t;
    (* Parent pointer is a singleton weak array *)
    mutable marginalized_parent : ('a, 'b) dsdistr Weak.t;
    mutable state : 'b rv_state;
    mutable distr : ('a, 'b) dsdistr;
  }

and 'a rv_state =
  | Initialized
  | Marginalized of ('a mdistr * ('a rv_from option))
  | Realized of 'a mtype

and ('a, 'b) dsdistr =
  | UDistr :  'b mdistr -> ('a, 'b) dsdistr
  | CDistr : ('z, 'm1) random_var * ('m1, 'm2) cdistr -> ('m1, 'm2) dsdistr

and 'b rv_from =
  RV_from : ('b, 'c) random_var -> 'b rv_from

let mdistr_to_distr (type a): a mdistr -> a Distribution.t = fun mdistr ->
  begin match mdistr with
    | MGaussian (mu, var) -> Distribution.gaussian mu (sqrt var)
    | MBeta (alpha, beta) -> Distribution.beta alpha beta
    | MBernoulli p -> Distribution.bernoulli p
  end

let cdistr_to_mdistr (type m) (type m'):
  (m, m') cdistr -> m mtype -> m' mdistr =
  fun cdistr obs ->
  begin match cdistr with
    | AffineMeanGaussian (m, b, obsvar) ->
        MGaussian (m *. obs +. b, obsvar)
    | CBernoulli ->
        MBernoulli obs
  end


let mgaussian mu var = MGaussian (mu, var)
let mbeta alpha beta = MBeta (alpha, beta)
let mbernoulli theta = MBernoulli theta

let affine_mean_gaussian m b var = AffineMeanGaussian (m, b, var)

let gaussian_mean_gaussian: float -> (mgaussiant, mgaussiant) cdistr =
  fun x ->
  AffineMeanGaussian (1., 0., x)

let make_marginal (type a) (type b): a mdistr -> (a, b) cdistr -> b mdistr =
  fun mdistr cdistr ->
  begin match mdistr, cdistr with
    | MGaussian (mu, var), AffineMeanGaussian(m, b, obsvar) ->
        MGaussian (m *. mu +. b, m ** 2. *. var +. obsvar)
    | MBeta (a, b),  CBernoulli ->
        MBernoulli (a /. (a +. b))
    | _ -> assert false (* error "impossible" *)
  end

let make_conditional (type a) (type b):
  a mdistr -> (a, b) cdistr -> b mtype -> a mdistr =
  let gaussian_conditioning mu var obs obsvar =
    let ivar = 1. /. var in
    let iobsvar = 1. /. obsvar in
    let inf = ivar +. iobsvar in
    let var' = 1. /. inf in
    let mu' = (ivar *. mu +. iobsvar *. obs) /. inf in
    (mu', var')
  in
  fun mdistr cdistr obs ->
  begin match mdistr, cdistr with
    | MGaussian(mu, var), AffineMeanGaussian(m, b, obsvar) ->
        let (mu', var') =
          gaussian_conditioning mu var ((obs -. b) /. m) (obsvar /. m ** 2.)
        in
        MGaussian(mu', var')
    | MBeta (a, b),  CBernoulli ->
        if obs then MBeta (a +. 1., b) else MBeta (a, b +. 1.)
    | _, _ -> assert false (* error "impossible" *)
  end

  (*
let finalfn (type a) (type b): (a, b) random_var -> unit =
    fun rvar ->
        print_string ("Finalizing: " ^ rvar.name ^ " \n")
;;
*)

  (*
let clone (type a) (type b) : ('a, 'b) random_var -> ('a, 'b) random_var = fun n ->
    let rec clone_helper (type a) (type b) : ('a, 'b) random_var -> unit =
        begin fun n ->
            let {name; shadow; children; marginalized_parent; state; distr} = n in
            assert (shadow = None);
            let ret = 
                {
                    name = name;
                    shadow = None;
                    children = Weak.create (Weak.length n.children);
                    marginalized_parent = Weak.create 1;
                    state = begin match n.state with
                        | Marginalized (dist, Some child) -> 
                            Marginalized (dist, clone_helper child)
                        | _ -> n.state
                    end ;
                    distr = begin match n.distr with
                        | CDistr (par, distr) -> CDistr (clone_helper par, distr)
                        | _ -> n.distr
                    end;
                }
            in
            n.shadow = Some ret;
        end
    in

    (* To be called with the _original_ node *)
    let rec set_weak (type a) (type b) : ('a, 'b) random_var -> unit =
        fun n ->
            let {name; shadow; children; marginalized_parent; state; distr} = n in
            begin match distr with
                | CDistr (par, _) -> set_weak par
                | _ -> ()
            end;

            begin match shadow with
                | Some n_s ->
                    let get n =
                        match n with
                        | Some o -> o
                        | None -> assert false
                    in
                    begin match Weak.get marginalized_parent 0 with
                        | Some par ->
                            Weak.set n_s.marginalized_parent 0 (Some (get par.shadow))
                        | None -> ()
                    end;

                    let rec set_children n = if n = Weak.length then () else
                        begin match Weak.get children n with
                            | Some child ->
                                Weak.set n_s.children n (Some (get child.shadow))
                            | None -> ()
                        end
                    in
                    set_children 0;
                | None -> assert false
            end
    in
    clone_helper;
    set_weak;
    begin match n.shadow with
    | Some n -> n
    | None -> assert false
    end
;;
*)


(* initialize without parent node *)
let assume_constant (type a) (type z): string -> a mdistr -> (z, a) random_var =
  fun n d ->
  (* Format.eprintf "assume_constant %s@." n; *)
  let ret = 
  { name = n;
    children = Weak.create 0;
    marginalized_parent = Weak.create 1;
    state = Marginalized (d, None);
    distr = UDistr d; }
  in
  ret
;;

(* initialize with parent node *)
let assume_conditional (type a) (type b) (type c):
  string -> (a,b) random_var -> (b, c) cdistr -> (b, c) random_var =
  fun str par cdistr ->
  (* Format.eprintf "assume_conditional %s@." str; *)

  let child =
    { name = str;
      children = Weak.create 0;
      marginalized_parent = Weak.create 1;
      state = Initialized;
      distr = CDistr (par, cdistr); }
  in

  let num_children = Weak.length par.children in
  let new_children = Weak.create (num_children + 1) in
  Weak.blit par.children 0 new_children 0 num_children;
  par.children <- new_children;
  Weak.set par.children num_children (Some (RV_from child));

  child
;;


let marginalize (type a) (type b): (a, b) random_var -> unit =
  fun n ->
  (* Format.eprintf "marginalize: %s@." n.name; *)
  begin match n.state, n.distr with
    | Initialized, CDistr (par, cdistr) ->
        let marg, new_parstate =
          begin match par.state with
            | Realized x ->
                (cdistr_to_mdistr cdistr x, Realized x)
            | Marginalized (par_marginal, None) ->
                (make_marginal par_marginal cdistr, Marginalized (par_marginal, Some (RV_from n)))
            | Marginalized (_, _)
            | Initialized -> assert false (* error "marginalize'" *)
          end
        in
        n.state <- Marginalized (marg, None);
        n.distr <- UDistr marg;
        Weak.set n.marginalized_parent 0 (Some (CDistr (par, cdistr)));
        par.state <- new_parstate
    | state, _ ->
        Format.eprintf "Error: marginalize %s@." n.name;
        assert false
  end

let rec delete :
  'a 'b. ('a, 'b) random_var -> 'a rv_from list -> 'a rv_from list =
  fun n l ->
  begin match l with
    | [] -> assert false
    | RV_from x :: l ->
        if Obj.repr x == Obj.repr n then l
        else RV_from x :: (delete n l)
  end

let realize (type a) (type b): b mtype -> (a, b) random_var -> unit =
  fun val_ n ->
  (* Format.eprintf "realize: %s@." n.name; *)
  (* ioAssert (isTerminal n) *)
  begin match Weak.get n.marginalized_parent 0 with
    | Some (UDistr _)
    | None -> ()
    | Some (CDistr (p, cdistr)) ->
      begin match p.state with
        | Marginalized (marg, _) ->
          let new_distr = make_conditional marg cdistr val_ in
          p.distr <- UDistr new_distr;
          p.state <- Marginalized (new_distr, None);
        | _ -> assert false (* error "realize" *)
      end
  end;
  
  n.state <- Realized val_;
    
  let rec marginalize_children i = if i = Weak.length n.children then () else
      begin match Weak.get n.children i with
      | None -> ()
      | Some (RV_from c) -> 
          marginalize c;
      end
  in

  marginalize_children 0;

  n.children <- Weak.create 0


let sample (type a) (type b) : (a, b) random_var -> unit =
  fun n ->
  (* Format.eprintf "sample: %s@." n.name; *)
  (* ioAssert (isTerminal n) *)
  begin match n.state with
    | Marginalized (m, _) ->
        let x = Distribution.draw (mdistr_to_distr m) in
        realize x n
    | _ -> assert false (* error "sample" *)
  end

let observe (type a) (type b): pstate -> b mtype -> (a, b) random_var -> unit =
  fun prob x n ->
  (* io $ ioAssert (isTerminal n) *)
  begin match n.state with
    | Marginalized (marg, _) ->
        factor (prob, Distribution.score (mdistr_to_distr marg) x);
        realize x n
    | _ -> assert false (* error "observe'" *)
  end

let is_marginalized state =
  begin match state with
  | Marginalized _ -> true
  | _ -> false
  end

(* Invariant 2: A node always has at most one marginal Child *)
let marginal_child (type a) (type b): (a, b) random_var -> b rv_from option =
  fun n ->
  match n.state with
  | Marginalized (_, mchild) -> mchild
  |_ -> assert false (* error "marginal_child" *)
;;

let rec prune : 'a 'b. ('a, 'b) random_var -> unit = function n ->
  (* Format.eprintf "prune: %s@." n.name; *)
  (* assert (isMarginalized (state n)) $ do *)
  begin match marginal_child n with
    | Some (RV_from child) ->
        prune child
    | None ->
        ()
  end;
  sample n

let rec graft : 'a 'b. ('a, 'b) random_var -> unit = function n ->
  (* Format.eprintf "graft %s@." n.name; *)
  begin match n.state with
  | Marginalized _ ->
      begin match marginal_child n with
        | Some (RV_from child) -> prune child
        | None -> ()
      end
  | _ ->
      begin match n.distr with
        | UDistr _ -> assert false (* error "graft" *)
        | CDistr (par, cdistr) ->
            graft par;
            marginalize n
      end
  end

let obs (type a) (type b): pstate -> b mtype -> (a, b) random_var -> unit =
  fun prob x n ->
  graft n;
  observe prob x n

let rec get_value: 'a 'b. ('a, 'b) random_var -> 'b mtype =
  fun n ->
  begin match n.state with
    | Realized x -> x
    | _ ->
        graft n;
        sample n;
        get_value n
  end

let draw (type a) (type b) : (a, b) random_var -> b mtype =
  fun n ->
  (* Format.eprintf "draw: %s@." n.name; *)
  graft n;
  (* ioAssert (isTerminal n) *)
  begin match n.state with
    | Marginalized (m, _) ->
        Distribution.draw (mdistr_to_distr m)
    | _ -> assert false (* error "sample" *)
  end

  (*
(* forget' :: IORef (Node a b) -> IO () *)
let forget (type a) (type b): (a, b) random_var -> unit =
  fun n ->
  (* Format.eprintf "forget: %s@." n.name; *)
  begin match n.state with
    | Realized _ -> ()
    | Initialized -> assert false (* error "forget" *)
    | Marginalized marg ->
        List.iter
          (fun (RV_from c) ->
             begin match c.distr with
               | UDistr d -> ()
               | CDistr (cdistr, par) ->
                   begin match c.state with
                     | Marginalized (marg, _) -> c.distr <- UDistr marg
                     | _ -> assert false (* error "forget" *)
                   end
             end)
          n.children;
        begin match n.distr with
          | UDistr _ -> ()
          | CDistr (cdistr, par) ->
              assert false (* error "forget: Shouldn't have parents?" *)
        end;
        n.distr <- UDistr marg
  end;
  n.children <- []
*)

let print_state n =   (* XXX TODO XXX *)
  Format.printf "%s: " n.name;
  begin match n.state with
  | Initialized -> Format.printf "Initialized"
  | Marginalized (MGaussian (mu, var), None) ->
      Format.printf "Marginalized (MGaussian (%f, %f), None)" mu var
  | Marginalized (MGaussian (mu, var), Some _) ->
      Format.printf "Marginalized (MGaussian (%f, %f), Some)" mu var
  | Marginalized _ -> Format.printf "Marginalized"
  | Realized x -> Format.printf "Realized %f" x
  end;
  Format.printf "@."


let observe_conditional (type a) (type b) (type c):
  pstate -> string -> (a, b) random_var -> (b, c) cdistr -> c mtype -> unit =
  fun prob str n cdistr observation ->
  let y = assume_conditional str n cdistr in
  obs prob observation y


(* ----------------------------------------------------------------------- *)
(* Examples *)

(* let delay_triplet zobs = *)
(*   let prob = { score = 0. } in *)
(*   let x = assume_constant "x" (MGaussian (0., 1.)) in *)
(*   Format.printf "x created@."; *)
(*   let y = assume_conditional "y"  x (gaussian_mean_gaussian 1.) in *)
(*   Format.printf "y created@."; *)
(*   let z = assume_conditional "z" y (gaussian_mean_gaussian 1.) in *)
(*   Format.printf "z created@."; *)
(*   obs prob zobs z; *)
(*   Format.printf "z observed@."; *)
(*   Format.printf "%f@." (get_value z); *)
(*   Format.printf "%f@." (get_value x); *)
(*   Format.printf "%f@." (get_value y) *)

(* let () = *)
(*   Random.self_init (); *)
(*   delay_triplet 42. *)

(* let obs_sample xobs = *)
(*   let prob = { Infer.scores = [| 0. |]; idx = 0 } in *)
(*   let x = assume_constant "x" (MGaussian (0., 1.)) in *)
(*   Format.printf "x created@."; *)
(*   obs prob xobs x; *)
(*   Format.printf "x observed@."; *)
(*   sample x; *)
(*   Format.printf "x sampled@."; *)
(*   Format.printf "%f@." (get_value x) *)

(* let () = *)
(*   Random.self_init (); *)
(*   obs_sample 42. *)

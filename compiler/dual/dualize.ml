open Lident
open Deftypes
open Hybrid

let rewrite context trans term sub =
  let sub' = trans sub in
    if sub == sub'
    then term
    else context sub'

let rewrite2 context trans1 trans2 term sub1 sub2 =
  let sub1' = trans1 sub1
  and sub2' = trans2 sub2 in
    if (sub1 == sub1') && (sub2 == sub2')
    then term
    else context sub1' sub2'

let rewrite3 context trans1 trans2 trans3 term sub1 sub2 sub3 =
  let sub1' = trans1 sub1
  and sub2' = trans2 sub2
  and sub3' = trans3 sub3 in
    if (sub1 == sub1') && (sub2 == sub2') && (sub3 == sub3')
    then term
    else context sub1' sub2' sub3'

let rewrite_list trans l0 =
  let rec rl =
    function
	[] as l -> l
      | (e::k) as l ->
	  let k' = rl k
	  and e' = trans e in
	    if (k == k') && (e == e')
	    then l
	    else e'::k'
  in rl l0

let rewrite_pair trans1 trans2 =
  function (x,y) as e ->
    rewrite2 (fun a b -> (a,b)) trans1 trans2 e x y

let dualize_float_const e =
  Eapp ((Eop (Modname { qual="Dual"; id="const" })),[e])

let dualize_qual q = q ^ "__dual"

let dualize_qualident { qual=q; id=i } = { qual=dualize_qual q; id=i }

let dualize_lident =
  function
      Modname q -> Modname (dualize_qualident q)
    | n -> n

let dualize_op =
  function
      (Eop n) as p -> rewrite (fun m -> Eop m) dualize_lident p n
    | p -> p

let dualize_typ =
  function { t_desc=d; t_index=i; t_level=j } as t ->
    rewrite
      (fun d' -> { t_desc=d'; t_index=i; t_level=j })
      dualize_typ_desc
      t
      d

and dualize_typ_desc =
  function
      Tvar as d -> d
    | (Tproduct  l) as d ->
	rewrite
	  (fun l' -> Tproduct l')
	  (rewrite_list dualize_typ)
	  d
	  l
    | (Tconstr (q,l,a)) as d ->
	rewrite3
	  (fun q' l' a' -> Tconstr (q',l',(ref a')))
	  dualize_qualident
	  (rewrite_list dualize_typ)
	  dualize_abbrev
	  d
	  q
	  l
	  (!a)
  | (Tlink t) as d ->
      rewrite
	(fun t' -> Tlink t')
	dualize_typ
	d
	t

and dualize_abbrev =
  function
      Tnil as a -> a
    | (Tcons (l,t)) as a ->
	rewrite2
	  (fun l' t' -> Tcons (l',t'))
	  (rewrite_list dualize_typ)
	  dualize_typ
	  a
	  l
	  t

let dualize_desc =
  function
      (Elocal _) as e -> e
    | (Eglobal n) as e -> rewrite (fun m -> Eglobal m) dualize_lident e n
    | (Econst (Efloat _)) as e -> dualize_float_const e
    | (Econst _) as e -> e
    | (Econstr0 n) as e -> rewrite (fun m -> Eglobal m) dualize_lident e n
    | (Elast _) as e -> e
    | (Eapp (p,l)) as e ->
	rewrite2
	  (fun (p',l') -> Eapp (p',l'))
	  dualize_op
	  (rewrite_list dualize_exp)
	  e
	  p
	  l
    | (Etuple l) as e ->
	rewrite
	  (fun l' -> Etuple l')
	  (rewrite_list dualize_exp)
	  e
	  l
    | (Erecord_access (f,n)) as e ->
	rewrite2
	  (fun f' n' -> Erecord_access (f',n'))
	  dualize_exp
	  dualize_lident
	  e
	  f
	  n
    | (Erecord l) as e ->
	rewrite
	  (fun l' -> Erecord l')
	  (rewrite_list
	      (rewrite_pair
		  dualize_lident
		  dualize_exp))
	  e
	  l
    | (Etypeconstraint (f,t)) as e ->
	rewrite2
	  (fun f' t' -> Etypeconstraint (f',t'))
	  dualize_exp
	  dualize_type_expression
	  e
	  f
	  t
    | (Elet (l,f)) as e ->
	rewrite2
	  (fun l' f' -> Elet (l,f))
	  dualize_local
	  dualize_exp
	  e
	  l
	  f
    | (Eseq (f,g)) as e ->
	rewrite2
	  (fun f' g' -> Eseq (f',g'))
	  dualize_exp
	  dualize_exp
	  e
	  f
	  g
    | (Eperiod _) as e -> e

and dualize_exp =
  function { e_desc=f; e_loc=l; e_typ=t } as e ->
    rewrite2
      (fun f' t' -> { e_desc=f'; e_loc=l; e_typ=t'})
      dualize_desc
      dualize_typ
      e
      f
      t

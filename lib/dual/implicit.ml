(*
 *
 * Defines implicit function f : x |--> y such that g(x,y)=0
 *
 *)

let implicit1 s g x y0 =
  let xr = Dual.re x
  and dx_dt = Dual.im x in
  let yr = s (g (Dual.const xr)) (Dual.re y0) in
  let dg_dx = Dual.im (g (Dual.make xr 1.) (Dual.const yr))
  and dg_dy = Dual.im (g (Dual.const xr) (Dual.make yr 1.)) in
  let dy_dx = ~-. dg_dx /. dg_dy in
  let dy_dt = dy_dx *. dx_dt in
    Dual.make yr dy_dt
    
(*
 *
 * Defines implicit function f : (x,y) |--> z such that g(x,y,z)=0
 *
 *)

let implicit2 s g x y z0 =
  let xr = Dual.re x
  and dx_dt = Dual.im x
  and yr = Dual.re y
  and dy_dt = Dual.im y in
  let zr = s (g (Dual.const xr) (Dual.const yr)) (Dual.re z0) in
  let dg_dx = Dual.im (g (Dual.make xr 1.) (Dual.const yr) (Dual.const zr))
  and dg_dy = Dual.im (g (Dual.const xr) (Dual.make yr 1.) (Dual.const zr))
  and dg_dz = Dual.im (g (Dual.const xr) (Dual.const yr) (Dual.make zr 1.)) in
  let dz_dx = ~-. dg_dx /. dg_dz
  and dz_dy = ~-. dg_dy /. dg_dz in
  let dz_dt = (dz_dx *. dx_dt) +. (dz_dy *. dy_dt) in
    Dual.make zr dz_dt
    

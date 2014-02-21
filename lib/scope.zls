open Basics

(*
  A plot window comprises one or more scopes.
  Each scope plots one or more signals.

  There are four plotting styles:

    linear              plot straight lines between successive samples

    points true         plot dots at the end of vertical lines ("lollipops")

    points false        plot dots

    piecewise           plot a horizontal line from the previous sample and
                        a dot for the current sample

    square              plot a horizontal line across from the previous sample
                        and then a vertical line to the current sample

  Scopes
  ------

  A scope is created by passing initial upper and lower limits for the y-axis,
  i.e. a default range for signal values, and a triple for each signal: name,
  type, value.

  For example, a scope for linear plotting of a single signal x with a default
  range of [-1.0, 1.0]:

    sig1 = scope (-1.0, 1.0, ("x", linear, x))

  For example, to additionally plot a discrete signal p:

    sig2 = scope2 (-1.0, 1.0, ("x", linear, x), ("p", discrete false, p))

  Windows
  -------

  A window is created by passing a name, an initial upper limit for the
  x-axis (i.e., the time), a flow of x-axis values (i.e., sample times), and one
  or more scopes.

  For example, a window called "model plot" with time horizon 20.0 and time
  values calculated in parallel for displaying the scope sig1:

    let rec t = 0.0 fby (t +. sample_period) in
    w1 = window ("model plot", 20.0, t, sig1)

  For example, to additionally plot the scope sig2:

    w2 = window2 ("model plot", 20.0, t, sig1, sig2)

*)

let piecewise  = Gtkplot.piecewise
let square     = Gtkplot.square
let linear     = Gtkplot.linear
let points x = Gtkplot.points x

let node scope (yl, yu, (n1, t1, v1)) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and sc = (Gtkplot.scope (yl, yu, singleton s1)) fby sc
  in
  Gtkplot.update (s1, v1);
  sc

let node scope2 (yl, yu, (n1, t1, v1), (n2, t2, v2)) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and sc = (Gtkplot.scope (yl, yu,
                           cons (s1, (singleton s2))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  sc

let node scope3 (yl, yu,
                 (n1, t1, v1), (n2, t2, v2), (n3, t3, v3)) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and s3 = (Gtkplot.signal (n3, t3)) fby s3
  and sc = (Gtkplot.scope (yl, yu,
                           cons (s1, (cons (s2, singleton s3)))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  Gtkplot.update (s3, v3);
  sc

let node scope4 (yl, yu,
                 (n1, t1, v1), (n2, t2, v2), (n3, t3, v3), (n4, t4, v4)) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and s3 = (Gtkplot.signal (n3, t3)) fby s3
  and s4 = (Gtkplot.signal (n4, t4)) fby s4
  and sc = (Gtkplot.scope (yl, yu,
                           cons (s1, (cons (s2, cons (s3, singleton s4))))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  Gtkplot.update (s3, v3);
  Gtkplot.update (s4, v4);
  sc

let node window (title, imaxt, v, s1) =
  let
  rec w = (Gtkplot.window (title, imaxt, singleton s1)) fby w
  in
  Gtkplot.tick (w, v)

let node window2 (title, imaxt, v, s1, s2) =
  let
  rec w = (Gtkplot.window (title, imaxt, cons (s1, singleton s2))) fby w
  in
  Gtkplot.tick (w, v)

let node window3 (title, imaxt, v, s1, s2, s3) =
  let
  rec w = (Gtkplot.window (title, imaxt,
             cons (s1, cons (s2, singleton s3)))) fby w
  in
  Gtkplot.tick (w, v)

let node window4 (title, imaxt, v, s1, s2, s3, s4) =
  let
  rec w = (Gtkplot.window (title, imaxt,
             cons (s1, cons (s2, cons (s3, singleton s4))))) fby w
  in
  Gtkplot.tick (w, v)

let node window5 (title, imaxt, v, s1, s2, s3, s4, s5) =
  let
  rec w = (Gtkplot.window (title, imaxt,
             cons (s1, cons (s2, cons (s3, cons (s4, singleton s5))))))
    fby w
  in
  Gtkplot.tick (w, v)


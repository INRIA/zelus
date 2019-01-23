let pi = 3.14

type motion_type = Stationary | Walking | Running

type walker = {
    position : float * float;
    velocity : float * float;
    motion_type : motion_type;
  }

let pos_noise = 0.01

let coast dt w =
  let both2 f (x, y) (x', y') = (f x x', f y y') in
  let both f (x, y) = (f x, f y) in
  let std_dev = sqrt dt *. pos_noise in
  let (x', y') = both2 (+.) w.position (both ( ( *. ) dt) w.velocity) in
  let x'' = Distribution.draw (Distribution.gaussian x' std_dev) in
  let y'' = Distribution.draw (Distribution.gaussian y' std_dev) in
  { w with position = (x'', y'') }

(* half lives of changing the motion type, in seconds *)
(* sometimes, we change to ourselves, to change direction *)
let motion_type_transition mt =
  begin match mt with
  | Stationary -> [(30., Walking); (60. *. 5., Running)]
  | Walking -> [(1., Walking); (10., Stationary); (60., Running)]
  | Running -> [(0.5, Running); (2., Walking)]
  end

let init_velocity mt =
  let speed_at_random_direction speed =
    let angle = Distribution.draw (Distribution.uniform_float 0. (2. *. pi)) in
    (speed *. cos angle, speed *. sin angle)
  in
  begin match mt with
  | Stationary -> (0., 0.)
  | Walking ->
      let speed = Distribution.draw (Distribution.uniform_float 0. 2.) in
      speed_at_random_direction speed
  | Running ->
      let speed = Distribution.draw (Distribution.uniform_float 2. 7.) in
      speed_at_random_direction speed
  end

(* (\* default units are seconds *\) *)
(* let motion dt w = *)
(*   let trans_lam = *)
(*     map (first (\x -> log 2 / x)) $ motionTypeTransition (motionType w) *)
(*   in *)
(*   let tTransition = *)
(*     Distribution.exponential (sum (map (recip . fst) trans_lam)) *)
(*   in *)
(*   if tTransition > dt *)
(*     then coast dt w *)
(*     else *)
(*       let w' = coast tTransition w in *)
(*       let mt = Data.Random.sample (Cat.fromWeightedList trans_lam) in *)
(*       let vel = init_velocity mt in *)
(*       motion (dt - tTransition) (w' { velocity = vel; motionType = mt }) *)

(* positionStdDev :: Double *)
(* positionStdDev = 10 *)

(* walkerMeasure :: Walker -> (Double, Double) -> PProg a () *)
(* walkerMeasure w (mx, my) = do *)
(*   factor (gaussian_ll x (positionStdDev^2) mx) *)
(*   factor (gaussian_ll y (positionStdDev^2) my) *)
(*   where *)
(*   (x, y) = position w *)

(* walkerGenMeasurement :: Walker -> RVar (Double, Double) *)
(* walkerGenMeasurement w = do *)
(*   mx <- normal x positionStdDev *)
(*   my <- normal y positionStdDev *)
(*   return (mx, my) *)
(*   where *)
(*   (x, y) = position w *)

(* walkerStep :: Double -> (Double, Double) -> Walker -> PProg a Walker *)
(* walkerStep dt measuredPosition w = do *)
(*   w' <- sample' (motion dt w) *)
(*   walkerMeasure w' measuredPosition *)
(*   return w' *)

(* walkerInit :: RVar Walker *)
(* walkerInit = do *)
(*   mt <- Data.Random.sample (Cat.fromWeightedList [(0.7 :: Double, Stationary), (0.25, Walking), (0.05, Running)]) *)
(*   vel <- initVelocity mt *)
(*   return (Walker { position = (0, 0), velocity = vel, motionType = mt }) *)

(* generateWalker :: Int -> RVar [(Double, (Double, Double))] *)
(* generateWalker n = do *)
(*   w <- walkerInit *)
(*   go n w *)
(*   where *)
(*   go 0 w = return [] *)
(*   go k w = do *)
(*     w' <- motion dt w *)
(*     mpos <- walkerGenMeasurement w' *)
(*     ((dt, mpos) :) <$> go (k - 1) w' *)
(*   dt = 10 *)

(* walkerSimulate :: [(Double, (Double, Double))] -> PProg Walker Walker *)
(* walkerSimulate measurements = do *)
(*   w <- sample' walkerInit *)
(*   go w measurements *)
(*   where *)
(*   go w [] = return w *)
(*   go w ((dt, measPos) : xs) = do *)
(*     w' <- walkerStep dt measPos w *)
(*     pyield w' *)
(*     go w' xs *)

(* frequencies :: (Eq a, Ord a) => [a] -> [(Double, a)] *)
(* frequencies = Cat.toList . Cat.fromObservations *)

(* runOurFilter :: PProg Walker a -> IO () *)
(* runOurFilter = void . runMStream (print . summarize) . particles 1000 *)
(*   where *)
(*   summarize :: [Walker] -> ([(Double, MotionType)], (Double, Double), (Double, Double)) *)
(*   summarize ws = *)
(*     (frequencies (map motionType ws), averagingBoth position, averagingBoth velocity) *)
(*     where *)
(*     averagingBoth f = (averaging (fst . f), averaging (snd . f)) *)
(*     averaging f = average (map f ws) *)

(* main :: IO () *)
(* main = do *)
(*   g <- getStdGen *)
(*   let (measurements, _) = sampleState (generateWalker 1000) g *)
(*   runOurFilter $ walkerSimulate measurements *)

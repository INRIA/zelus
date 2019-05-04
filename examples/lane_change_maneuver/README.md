<!-- Author: François Bidet -->

# Lane change maneuver for autonomous vehicles

Model presented in the article "Lane change maneuver for autonomous vehicles (Benchmark proposal)" at ARCH18 Workshop on Applied Verification of Continuous and Hybrid Systems.

## Adaptation
- only linearized dynamic of vehicles, using rounded values presented in the article, produces good results
- measurement errors and disturbance are generated every 0.5 (_Constants.dt\_noise_ value) seconds calling "Random" module
- reference values given in the article are not in the international system of units (SI): km/h as to be converted in m/s and angle degrees to radians
- reference position of the interior vehicle is changed from the one given in the article:
  $$
  x^{(2)}_{r,ref} = max(...,\ x^{(2)}_r - t_{gap} \cdot v^{(2)}_x)
  $$
  is replaced by
  $$
  x^{(2)}_{r,ref} = max(...,\ x^{(3)}_r - t_{gap} \cdot v^{(3)}_x)
  $$
  to take into account leader position

## Output
- Drawing (OCaml module "Graphics")
- CSV on standard output: \ \ \ time, x~rear~, y~rear~, x~interior~, y~interior~, x~leader~, y~leader~, x~merging~, y~merging~

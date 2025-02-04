include Node_base

module Ode23Solver = Make (Solvers.Ode23) (Illinois)
module Ode45Solver = Make (Solvers.Ode45) (Illinois)
module SundialsSolver = Make (Solvers.Sundials_cvode) (Illinois)

let solve_ode23 = Ode23Solver.solve
let solve_ode45 = Ode45Solver.solve
let solve = SundialsSolver.solve

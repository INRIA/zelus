open Owl

type vector = Mat.mat
type matrix = Mat.mat

module Mat = struct
  let add = Owl.Mat.add
  let sub = Owl.Mat.sub
  let dot = Owl.Mat.dot
  let transpose = Owl.Mat.transpose
  let scalar_mul = Owl.Mat.scalar_mul
  let eye = Owl.Mat.eye
  let zeros = Owl.Mat.zeros
end

module Linalg = struct
  let inv = Owl.Linalg.D.inv
end


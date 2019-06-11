def sumAlg: ListF[Double, Double] => Double = {
  case ConsF(e, s) => e + s
  case NilF => 0.0
}
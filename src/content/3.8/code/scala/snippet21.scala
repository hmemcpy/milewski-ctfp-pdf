def lenAlg[E]: ListF[E, Int] => Int = {
  case ConsF(e, n) => n + 1
  case NilF => 0
}
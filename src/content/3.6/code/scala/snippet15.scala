def lambda[A]: ((Unit, A)) => A = {
  case ((), x) => x
}
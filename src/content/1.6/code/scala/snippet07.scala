def rho[A]: ((A, Unit)) => A = {
  case (x, ()) => x
}
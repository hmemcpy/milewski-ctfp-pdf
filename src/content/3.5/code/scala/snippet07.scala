def runReader[E, A]: Reader[E, A] => E => A = {
  case Reader(f) => e => f(e)
}
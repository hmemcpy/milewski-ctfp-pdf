def runCont[R, A]: Cont[R, A] => (A => R) => R = {
  case Cont(k) => h => k(h)
}
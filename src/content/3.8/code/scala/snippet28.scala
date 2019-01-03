def era: List[Int] => StreamF[Int, List[Int]] = {
  case p :: ns =>
    def notdiv(p: Int)(n: Int): Boolean =
      n % p != 0
    StreamF(p, ns.filter(notdiv(p)))
}

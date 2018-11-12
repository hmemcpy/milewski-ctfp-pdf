def sum(l: List[Double]): Double =
  l.foldRight(0.0)((e, s) => e + s)
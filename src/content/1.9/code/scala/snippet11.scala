val f: Either[Int, Double] => String = {
  case Left(n) => if (n < 0) "Negative int" else "Positive int"
  case Right(x) => if (x < 0.0) "Negative double" else "Positive double"
}
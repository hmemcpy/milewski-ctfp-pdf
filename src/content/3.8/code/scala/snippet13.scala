def unFix[F[_]]: Fix[F] => F[Fix[F]] = {
  case Fix(x) => x
}
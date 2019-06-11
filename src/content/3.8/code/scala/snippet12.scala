object Fix {
  def apply[F[_]](f: F[Fix[F]]): Fix[F] = new Fix(f)
}
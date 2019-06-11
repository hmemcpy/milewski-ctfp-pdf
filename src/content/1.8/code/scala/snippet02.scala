implicit val tuple2Bifunctor = new Bifunctor[Tuple2] {
  override def bimap[A, B, C, D](f: A => C)(g: B => D): ((A, B)) => (C, D) = {
    case (x, y) => (f(x), g(y))
  }
}
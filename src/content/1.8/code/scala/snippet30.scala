implicit val function1Profunctor = new Profunctor[Function1] {
  override def bimap[A, B, C, D]: (A => B) => (C => D) => (B => C) => (A => D) = ab => cd => bc =>
    cd compose bc compose ab

  override def lmap[A, B, C]: (A => B) => (B => C) => (A => C) =
    flip(compose)

  override def rmap[A, B, C]: (B => C) => (A => B) => (A => C) =
    compose
}
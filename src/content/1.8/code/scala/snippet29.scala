trait Profunctor[F[_, _]] {
  def dimap[A, B, C, D]: (A => B) => (C => D) => F[B, C] => F[A, D] = f => g =>
    lmap(f) compose rmap[B, C, D](g)

  def lmap[A, B, C]: (A => B) => F[B, C] => F[A, C] = f =>
    dimap(f)(identity[C])

  def rmap[A, B, C]: (B => C) => F[A, B] => F[A, C] =
    dimap[A, A, B, C](identity[A])
}

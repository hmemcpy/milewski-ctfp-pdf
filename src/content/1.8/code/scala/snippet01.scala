trait Bifunctor[F[_, _]] {
  def bimap[A, B, C, D](g: A => C)(h: B => D): F[A, B] => F[C, D] =
    first(g) compose second(h)

  def first[A, B, C](g: A => C): F[A, B] => F[C, B] =
    bimap(g)(identity[B])

  def second[A, B, D](h: B => D): F[A, B] => F[A, D] =
    bimap(identity[A])(h)
}
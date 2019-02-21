implicit def arrowProfunctor = new Profunctor[Function1] {
  def dimap[A, B, C, D](ab: A => B)(cd: C => D)(bc: B => C): A => D =
    cd compose bc compose ab

  def lmap[A, B, C](f: C => A)(ab: A => B): C => B =
    f andThen ab

  def rmap[A, B, C](f: B => C)(ab: A => B): A => C =
    f compose ab
}
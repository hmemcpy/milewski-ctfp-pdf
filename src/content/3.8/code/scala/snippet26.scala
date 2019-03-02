case class StreamF[E, A](h: E, t: A)

implicit def streamFFunctor[E] = new Functor[StreamF[E, ?]] {
  def fmap[A, B](f: A => B)(fa: StreamF[E, A]): StreamF[E, B] =
    ...
}
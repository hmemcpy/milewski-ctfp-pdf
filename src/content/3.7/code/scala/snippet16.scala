final case class Stream[A](
    h: () => A,
    t: () => Stream[A]
)
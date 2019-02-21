case class Stream[X](
  h: () => X,
  t: () => Stream[X]
)
implicit val streamComonad = new Comonad[Stream] {
  def extract[A](wa: Stream[A]): A =
    wa match {
      case Stream(a, _) => a()
    }

  def duplicate[A](wa: Stream[A]): Stream[Stream[A]] = wa match {
    case s @ Stream(a, as) =>
      Stream(() => s, () => duplicate(as()))
  }
}
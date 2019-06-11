def duplicateS[A](wa: Stream[A]): Stream[Stream[A]] = wa match {
  case s @ Stream(a, as) =>
    Stream(() => s, () => duplicateS(as()))
}
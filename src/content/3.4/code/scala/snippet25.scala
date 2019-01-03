def process: String => Writer[String, List[String]] = s => {
  import moreSyntax._
  upCase(s) flatMap (upStr =>
    tell("toWords ") >>
      writerMonad.pure(words(upStr)))
}
def process: String => Writer[String, List[String]] =
  s => {
    upCase(s).flatMap { upStr =>
      tell("toWords ").flatMap { _ =>
        writerMonad.pure(words(upStr))
      }
    }
  }
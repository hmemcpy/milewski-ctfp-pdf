def process: String => Writer[String, List[String]] =
  s => {
    import bindSyntax._
    for {
      upStr <- upCase(s)
      words <- toWords(upStr)
    } yield words
  }
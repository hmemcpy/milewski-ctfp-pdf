def process: String => Writer[String, List[String]] =
  s => {
    import bindSyntax._
    upCase(s) >>= (upStr => toWords(upStr))
  }
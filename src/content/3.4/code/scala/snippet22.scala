def words: String => List[String] =
  _.split("\\s+").toList

def process: String => Writer[String, List[String]] =
  s => {
    import bindSyntax._
    for {
      upStr <- upCase(s)
      _ <- tell("toWords ")
    } yield words(upStr)
  }
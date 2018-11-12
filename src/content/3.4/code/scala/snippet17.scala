def toWords: String => Writer[String, List[String]] =
  s => Writer(s.split("\\s+").toList, "toWords ")

def process: String => Writer[String, List[String]] = {
  import kleisliSyntax._
  // -Ypartial-unification should be on
  upCase >=> toWords
}
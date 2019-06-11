val upCase: String => Writer[String] =
  s => (s.toUpperCase, "upCase ")

val toWords: String => Writer[List[String]] =
  s => (s.split(' ').toList, "toWords ")
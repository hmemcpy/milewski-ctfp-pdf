val toWords: String => Writer[List[String]] =
  s => (s.split(' ').toList, "toWords ")
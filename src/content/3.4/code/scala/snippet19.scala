def upCase: String => Writer[String, String] =
  s => Writer(s.toUpperCase, "upCase ")
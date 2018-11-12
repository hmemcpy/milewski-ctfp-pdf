val upCase: String => Writer[String] =
  s => (s.toUpperCase, "upCase ")
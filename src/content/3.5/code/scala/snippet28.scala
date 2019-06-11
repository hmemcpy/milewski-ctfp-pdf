runCont(ka) { a =>
  val kb = kab(a)
  runCont(kb)(hb)
}
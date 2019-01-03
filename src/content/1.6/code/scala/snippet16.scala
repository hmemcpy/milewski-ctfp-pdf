val tupleToElem: ((String, String, Int)) => Element = {
  case (n, s, a) => Element(n, s, a)
}
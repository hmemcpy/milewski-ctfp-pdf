val elemToTuple: Element => (String, String, Int) =
  e => (e.name, e.symbol, e.atomicNumber)
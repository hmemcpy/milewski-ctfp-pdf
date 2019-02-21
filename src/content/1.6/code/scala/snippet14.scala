val startsWithSymbol: ((String, String, Int)) => Boolean = {
  case (name, symbol, _) => name.startsWith(symbol)
}
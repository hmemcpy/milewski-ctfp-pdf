let starts_with_symbol = ((name, symbol, _)) =>
  String.is_prefix(name, ~prefix=symbol);

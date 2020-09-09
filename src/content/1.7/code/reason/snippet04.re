let f' = f =>
  fun
  | None => None
  | Some(x) => Some(f(x));

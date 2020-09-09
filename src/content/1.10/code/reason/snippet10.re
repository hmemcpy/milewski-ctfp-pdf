let rec fmap = f =>
  fun
  | [] => []
  | [x, ...xs] => [f(x), ...fmap(f, xs)];

let safe_head =
  fun
  | [] => None
  | [x, ...xs] => Some(x);

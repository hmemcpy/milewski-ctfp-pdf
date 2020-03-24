let maybe_tail =
  fun
  | [] => None
  | [_, ...xs] => Some(xs);

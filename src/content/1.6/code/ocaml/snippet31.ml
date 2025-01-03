let tail_option = function
  | Nil -> None
  | Cons (_, xs) -> Some xs

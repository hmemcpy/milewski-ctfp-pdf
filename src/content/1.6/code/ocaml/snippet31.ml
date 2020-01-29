type 'a maybe =
  | Nothing
  | Just of 'a

let maybe_tail = function
  | Nil -> Nothing
  | Cons (_, xs) -> Just xs
;;

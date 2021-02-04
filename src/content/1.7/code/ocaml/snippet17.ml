let rec fmap f = function
  | Nil -> Nil
  | Cons (x, xs) -> Cons (f x, fmap f xs)
;;

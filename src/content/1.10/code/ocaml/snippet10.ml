let rec fmap f = function
  | [] -> []
  | x :: xs -> f x :: fmap f xs
;;

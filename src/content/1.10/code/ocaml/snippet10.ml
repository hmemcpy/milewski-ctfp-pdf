module ListFunctor : Functor with type 'a t = 'a list = struct
  type 'a t = 'a list
  let rec fmap f = function
    | [] -> []
    | x :: xs -> f x :: fmap f xs
end

module List_Functor : Functor with type 'a t = 'a list = struct
  type 'a t = 'a list

  let rec fmap f = function
    | Nil -> Nil
    | Cons (x, xs) -> Cons (f x, fmap f xs)
  ;;
end

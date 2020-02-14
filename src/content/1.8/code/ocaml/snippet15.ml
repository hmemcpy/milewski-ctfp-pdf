module TreeFunctor : Functor = struct
  type 'a t = 'a tree

  let rec fmap f = function
    | Leaf a -> Leaf (f a)
    | Node (l, r) -> Node (fmap f l, fmap f r)
  ;;
end

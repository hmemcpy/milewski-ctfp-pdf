module TreeFunctor : Functor with type 'a t = 'a tree = struct
  type 'a t = 'a tree

  let rec fmap f = function
    | Leaf a -> Leaf (f a)
    | Node (l, r) -> Node (fmap f l, fmap f r)
end

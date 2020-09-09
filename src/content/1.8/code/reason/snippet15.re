module TreeFunctor: Functor = {
  type t('a) = tree('a);
  
  let rec fmap = f =>
    fun
    | Leaf(a) => Leaf(f(a))
    | Node(l, r) => Node(fmap(f, l), fmap(f, r));
};

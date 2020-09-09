module StreamFunctor: Functor with type t('a) = stream('a) = {
  type t('a) = stream('a);

  let rec fmap = f =>
    fun
    | Cons(x, xs) => Cons(f(x), Lazy.from_val(fmap(f, Lazy.force(xs))));
};

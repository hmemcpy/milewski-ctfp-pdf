module List_Functor: Functor with type t('a) = list('a) = {
  type t('a) = list('a);
  
  let rec fmap = f =>
    fun
    | Nil => Nil
    | Cons(x, xs) => Cons(f(x), fmap(f, xs));
};

module Option_Functor: Functor with type t('a) = option('a) = {
  type t('a) = option('a);
  
  let fmap = f =>
    fun
    | None => None
    | Some(x) => Some(f(x));
};

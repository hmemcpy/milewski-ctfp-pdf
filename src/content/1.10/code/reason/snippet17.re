module Reader_Functor = (T: {type e;}) : Functor => {
  type t('a) = reader(T.e, 'a);
  
  let fmap: 'a 'b. ('a => 'b, t('a)) => t('b) =
    f =>
      fun
      | Reader(r) => Reader(compose(f, r));
};

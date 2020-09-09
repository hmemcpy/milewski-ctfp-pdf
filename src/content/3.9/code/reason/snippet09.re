module Store_Functor = (S: {type s;}) : 
       (Functor with type t('a) = store(S.s, 'a)) => {
  type w('a) = store(S.s, 'a);
  type t('a) = w('a);

  let fmap = (g, Store(f, s)) => Store(compose(g, f), s);
};

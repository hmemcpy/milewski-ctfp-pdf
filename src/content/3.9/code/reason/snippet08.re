module Store_comonad =
       (S: {type s;}, F: Functor with type t('a) = store(S.s, 'a))
       : (Comonad with type w('a) = store(S.s, 'a)) => {
  type w('a) = store(S.s, 'a);

  include F;

  let extract: w('a) => 'a = ((Store(f, s)) => f(s): w('a) => 'a);

  let duplicate: w('a) => w(w('a)) = (
    (Store(f, s)) => Store(s => Store(f, s), s): w('a) => w(w('a))
  );
};

module StoreComonadBase =
       (S: {type s;}, F: Functor with type t('a) = store(S.s, 'a))
       : (ComonadBase with type w('a) = store(S.s, 'a)) => {
  type w('a) = store(S.s, 'a);

  include F;

  let extract = (Store(f, s)) => f(s);
};

module StoreComonadDuplicate =
       (S: {type s;})
       : (ComonadDuplicate with type w('a) = store(S.s, 'a)) => {
  type w('a) = store(S.s, 'a);

  let duplicate = (Store(f, s)) => Store(make_store(f), s);
};

/* Generate Full comonad */
module StoreComonad =
       (S: {type s;}, F: Functor with type t('a) = store(S.s, 'a))
       : (Comonad with type w('a) = store(S.s, 'a)) =>
  ComonadImplViaExtend(
    (StoreComonadBase(S, F)),
    (StoreComonadDuplicate(S)),
  );

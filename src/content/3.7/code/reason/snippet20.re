/* Implement Extract */
module StreamComonadBase =
       (F: Functor with type t('a) = stream('a))
       : (ComonadBase with type w('a) = stream('a)) => {
  type w('a) = stream('a);

  include F;

  let extract = (Cons(x, _)) => x;
};

/* Implement duplicate */
module StreamComonadDuplicate: ComonadDuplicate with type w('a) =
    stream('a) = {
  type w('a) = stream('a);

  let rec duplicate = (Cons(x, xs)) =>
    Cons(Cons(x, xs), Lazy.from_val(duplicate(Lazy.force(xs))));
};

/* Generate full Comonad Instance */
module StreamComonad: Comonad with type w('a) = stream('a) =
  ComonadImplViaExtend(
    (StreamComonadBase(StreamFunctor)),
    StreamComonadDuplicate,
  );

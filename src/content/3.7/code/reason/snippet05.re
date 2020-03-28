module type Comonad = {
  type w('a);

  include Functor with type t('a) := w('a);

  let extract: w('a) => 'a;
  let (=>=): (w('a) => 'b, w('b) => 'c, w('a)) => 'c;
};

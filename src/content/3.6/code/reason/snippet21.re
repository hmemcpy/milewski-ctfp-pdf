module AdjunctionState = (
      S: {type s;},
      F: Functor with type t('a) = prod(S.s, 'a),
      R: Representable with type t('a) = reader(S.s, 'a),
    ): Adjunction => {
  type f('a) = prod(S.s, 'a);
  type r('a) = reader(S.s, 'a);

  include F;
  include R;

  let unit = a => Reader(s => Prod(a, s));
  let counit = (Prod(Reader(f), s)) => f(s);
};

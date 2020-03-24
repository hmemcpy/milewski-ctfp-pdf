module OpContravariant = (T: {type r;}) : Contravariant => {
  type t('a) = op(T.r, 'a);

  let contramap = (f, h, b) => h(f(b));
};

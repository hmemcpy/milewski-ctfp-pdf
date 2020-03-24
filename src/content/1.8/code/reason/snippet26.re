module OpContravariant = (In: {type r;}) : Contravariant => {
  type t('a) = op(In.r, 'a);
  
  let contramap = (f, g) => compose(g, f);
};

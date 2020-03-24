module Op_Contravariant = (T: {type r;}) : Contravariant => {
  type t('a) = op(T.r, 'a);

  let contramap: ('b => 'a, t('a)) => t('b) =
    f =>
      fun
      | Op(g) => Op(compose(g, f));
};

module type Contravariant = {
  type t('a);
  let contramap: ('b => 'a, t('a)) => t('b);
};

type tostring('a) =
  | ToString('a => string);

module ToStringInstance: Contravariant = {
  type t('a) = tostring('a);
  
  let contramap = (f, ToString(g)) => ToString(compose(g, f));
};

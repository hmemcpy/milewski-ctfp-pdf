module type Functor = {
  type t('a);

  let fmap: ('a => 'b, t('a)) => t('b);
};

module type Profunctor = {
  type p('a, 'b);

  let dimap: ('c => 'a, 'b => 'd, p('a, 'b)) => p('c, 'd);
};

let id = a => a;

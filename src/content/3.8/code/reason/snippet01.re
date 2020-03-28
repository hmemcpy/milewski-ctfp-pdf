module type Algebra =
  (F: {type f('a);}) => {type algebra('a) = F.f('a) => 'a;};

module ProfunctorArrow: Profunctor = {
  type p('a, 'b) = 'a => 'b;
  
  let dimap = (f, g, p) => compose(g, compose(p, f));
  let lmap = (f, p) => (flip(compose))(f, p);
  let rmap = compose;
};

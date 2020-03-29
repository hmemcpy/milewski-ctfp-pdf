module type Polymorphic_Projection = (P: Profunctor) => {
  type rank2_p = {p: 'c. P.p('c, 'c)};

  let pi: rank2_p => P.p('a, 'b);
};

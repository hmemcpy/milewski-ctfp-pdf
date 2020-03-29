module Pi = (P: Profunctor) => {
  type rank2_p = {p: 'a. P.p('a, 'a)};

  let pi: rank2_p => P.p('c, 'c) = (e => e.p: rank2_p => P.p('c, 'c));
};

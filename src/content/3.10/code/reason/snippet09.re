module EndsEqualizer = (P: Profunctor) => {
  let lambda: (P.p('a, 'a), 'a => 'b) => P.p('a, 'b) = (
    (paa, f) => P.dimap(id, f, paa)
  );

  let rho: (P.p('b, 'b), 'a => 'b) => P.p('a, 'b) = (
    (pbb, f) => P.dimap(f, id, pbb)
  );
};

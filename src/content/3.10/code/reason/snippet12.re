module EndsWithDiaProd = (
    P: Profunctor,
    D: DiaProd with type p('a, 'b) = P.p('a, 'b),
    PP: ProdP with type p('a, 'b) = P.p('a, 'b),
  ) => {
  module E = EndsEqualizer(P);

  let lambdaP: D.diaprod('a) => PP.prod_p('a, 'b) = (
    (DiaProd(paa)) => E.lambda(paa)
  );

  let rhoP: D.diaprod('b) => PP.prod_p('a, 'b) = (
    (DiaProd(pbb)) => E.rho(pbb)
  );
};

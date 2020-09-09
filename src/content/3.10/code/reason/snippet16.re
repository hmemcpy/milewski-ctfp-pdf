module type DiagSum = {
  type a;
  type p('a, 'b);

  let paa: p(a, a);
};

module CoEndImpl = (P: Profunctor) => {
  type a;
  type b;

  module type Sum_P =
    SumP with type p('a, 'b) = P.p('a, 'b)
      and type a = a and type b = b;

  let lambda = (module S: Sum_P): (module DiagSum) =>
    (module {
       type a = S.b;
       type p('a, 'b) = P.p('a, 'b);

       let paa = P.dimap(S.f, id, S.pab);
     });

  let rho = (module S: Sum_P): (module DiagSum) =>
    (module {
       type a = S.a;
       type p('a, 'b) = P.p('a, 'b);

       let paa = P.dimap(id, S.f, S.pab);
     });
};

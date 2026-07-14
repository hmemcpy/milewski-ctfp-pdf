module EndsWithDiaProd
    (P : Profunctor)
    (D : DiaProd with type ('a, 'b) t = ('a, 'b) P.t)
    (PP : ProdP with type ('a, 'b) t = ('a, 'b) P.t) =
struct
  module E = EndsEqualizer (P)

  let lambdaP : 'a D.diaprod -> ('a, 'b) PP.prod_p =
   fun (DiaProd paa) -> E.lambda paa

  let rhoP : 'b D.diaprod -> ('a, 'b) PP.prod_p =
    fun (DiaProd pbb) -> E.rho pbb
end

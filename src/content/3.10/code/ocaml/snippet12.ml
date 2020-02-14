module EndsWithDiaProd
    (P : Profunctor)
    (D : DiaProd with type ('a, 'b) p = ('a, 'b) P.p)
    (PP : ProdP with type ('a, 'b) p = ('a, 'b) P.p) =
struct
  module E = EndsEqualizer (P)

  let lambdaP : 'a D.diaprod -> ('a, 'b) PP.prod_p =
   fun (DiaProd paa) -> E.lambda paa
 ;;

  let rhoP : 'b D.diaprod -> ('a, 'b) PP.prod_p =
   fun (DiaProd pbb) -> E.rho pbb
 ;;
end

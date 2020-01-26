module type DiagSum = sig
  type a
  type ('a, 'b) p

  val paa : (a, a) p
end

module CoEndImpl (P : Profunctor) = struct
  type a
  type b

  module type Sum_P =
    SumP
      with type ('a, 'b) p = ('a, 'b) P.p
       and type a = a
       and type b = b

  let lambda (module S : Sum_P) =
    (module struct
      type a = S.b
      type ('a, 'b) p = ('a, 'b) P.p

      let paa = P.dimap S.f id S.pab
    end : DiagSum)
  ;;

  let rho (module S : Sum_P) =
    (module struct
      type a = S.a
      type ('a, 'b) p = ('a, 'b) P.p

      let paa = P.dimap id S.f S.pab
    end : DiagSum)
  ;;
end

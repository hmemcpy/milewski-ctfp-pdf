module type Polymorphic_Projection = functor (P : Profunctor) -> sig
  type rank2_p = { p : 'c. ('c, 'c) P.p }

  val pi : rank2_p -> ('a, 'b) P.p
end

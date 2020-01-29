module type FreeMonoidRep = functor (F : Functor) -> sig
  type x
  type n

  val q : x -> n F.t
end

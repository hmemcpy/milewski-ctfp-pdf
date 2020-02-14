module type FreeMonoidRep = functor (F : Functor) -> sig
  type x
  type m

  val p : x -> m F.t
end

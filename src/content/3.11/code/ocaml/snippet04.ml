module type Lst = sig
  type a
  type m

  module M : Monoid with type m = m

  type lst = (a -> M.m) -> M.m

  val f : lst
end

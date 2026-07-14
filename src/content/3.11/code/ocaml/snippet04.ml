module type Lst = sig
  type a
  type m

  module M : Monoid with type t = m

  type lst = (a -> M.t) -> M.t

  val f : lst
end

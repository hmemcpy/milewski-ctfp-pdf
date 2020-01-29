module type Adjunction_HomSet = functor
  (F : Functor)
  (U : Representable)
  -> sig
  val left_adjunct : ('a F.t -> 'b) -> 'a -> 'b U.t
  val right_adjunct : ('a -> 'b U.t) -> 'a F.t -> 'b
end

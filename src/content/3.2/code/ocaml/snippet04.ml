(* L is Functor F and R is Representable Functor U *)
module type Adjunction = functor
  (F : Functor)
  (U : Representable)
  -> sig
  val unit : 'a -> 'a F.t U.t
  val counit : 'a U.t F.t -> 'a
end

module type Monad_Join = functor (F : Functor) -> sig
  type 'a m = 'a F.t

  val join : 'a m m -> 'a m
  val return : 'a -> 'a m
end

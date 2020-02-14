module type Monad = sig
  type 'a m

  val ( >=> ) : ('a -> 'b m) -> ('b -> 'c m) -> 'a -> 'c m
  val return : 'a -> 'a m
end

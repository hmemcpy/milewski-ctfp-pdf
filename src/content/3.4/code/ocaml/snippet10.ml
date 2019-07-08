module type Monad_Bind = sig
  type 'a m

  val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
  val return : 'a -> 'a m
end

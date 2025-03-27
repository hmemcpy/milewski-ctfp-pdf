module type Monad = sig
  type 'a t

  val ( >=> ) : ('a -> 'b t) -> ('b -> 'c t) -> 'a -> 'c t
  val return : 'a -> 'a t
end

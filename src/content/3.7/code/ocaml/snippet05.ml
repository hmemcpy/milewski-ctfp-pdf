module type Comonad = sig
  type 'a w

  include Functor with type 'a t := 'a w

  val extract : 'a w -> 'a
  val ( =>= ) : ('a w -> 'b) -> ('b w -> 'c) -> 'a w -> 'c
end

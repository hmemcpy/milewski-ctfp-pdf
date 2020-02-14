module type CoKleisli = sig
  type 'a w

  val ( =>= ) : ('a w -> 'b) -> ('b w -> 'c) -> 'a w -> 'c
end

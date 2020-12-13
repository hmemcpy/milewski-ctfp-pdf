module type Reader_Fmap_Example = sig
  val fmap : ('a -> 'b) -> ('r -> 'a) -> 'r -> 'b
end

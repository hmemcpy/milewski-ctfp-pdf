module type Const_Functor_Example = sig
  val fmap : ('a -> 'b) -> ('c, 'a) const -> ('c, 'b) const
end

module type Monoid = sig
  type m

  val mappend : m -> m -> m
  val mempty : m
end

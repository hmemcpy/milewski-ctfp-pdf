module type Monoid = sig
  type m

  val mempty : m
  val mappend : m -> m -> m
end

module type Monoid = sig
  type a

  val mempty : a
  val mappend : a -> a -> a
end

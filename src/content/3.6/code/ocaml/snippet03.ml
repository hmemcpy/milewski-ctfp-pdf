module type Monoid = sig
  type t

  val mappend : t -> t -> t
  val mempty : t
end

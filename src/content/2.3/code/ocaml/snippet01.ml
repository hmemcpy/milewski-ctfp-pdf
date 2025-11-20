module type Monoid = sig
  type t

  val mempty : t
  val mappend : t -> t -> t
end

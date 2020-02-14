module type Comonoid = sig
  type m

  val split : m -> m * m
  val destroy : m -> unit
end

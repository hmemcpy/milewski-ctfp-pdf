module type AtoB = sig
  type a
  type b

  val f : a -> b
end

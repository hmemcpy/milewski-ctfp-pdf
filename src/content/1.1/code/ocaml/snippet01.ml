module type Polymorphic_Function_F = sig
  type a
  type b

  val f : a -> b
end

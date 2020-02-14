module type Polymorphic_Function_G = sig
  type b
  type c

  val g : b -> c
end

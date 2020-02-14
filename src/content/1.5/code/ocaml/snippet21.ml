module type CoProduct = sig
  type a
  type b
  type c

  val i : a -> c
  val j : b -> c
end

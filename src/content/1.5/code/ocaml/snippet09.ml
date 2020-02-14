module type Chapter5_Product = sig
  type a
  type c
  type b

  val p : c -> a
  val q : c -> b
end

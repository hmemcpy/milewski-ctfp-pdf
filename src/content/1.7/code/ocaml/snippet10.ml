module type Eq = sig
  type a

  val ( == ) : a -> a -> bool
end

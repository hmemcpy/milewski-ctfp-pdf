module type FreeF_Alt = sig
  type a
  type 'a f

  val freeF : (a -> 'i) -> 'i f
end

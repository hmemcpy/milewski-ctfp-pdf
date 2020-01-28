module type FreeF = sig
  type 'a f
  type a
  type i

  val h : i -> a
  val fi : i -> i f
end

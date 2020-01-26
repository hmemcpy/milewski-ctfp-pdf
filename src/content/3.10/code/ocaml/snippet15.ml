module type SumP = sig
  type a
  type b
  type ('a, 'b) p

  val f : b -> a
  val pab : (a, b) p
end

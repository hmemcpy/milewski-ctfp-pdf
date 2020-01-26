module type DiagSum = sig
  type a
  type ('a, 'b) p

  val paa : (a, a) p
end

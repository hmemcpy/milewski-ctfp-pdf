module type Unit_Example = sig
  type 'a m

  val return : 'd -> 'd m
end

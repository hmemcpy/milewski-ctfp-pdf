module type Unit_Example = sig
  type 'd m

  val return : 'd -> 'd m
end

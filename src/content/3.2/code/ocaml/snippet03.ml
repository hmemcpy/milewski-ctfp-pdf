module type Counit_Example = sig
  type 'c w

  val extract : 'c w -> 'c
end

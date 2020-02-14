module type Representable = sig
  type 'x t
  type rep (* Representing type 'a' *)

  val tabulate : (rep -> 'x) -> 'x t
  val index : 'x t -> rep -> 'x
end

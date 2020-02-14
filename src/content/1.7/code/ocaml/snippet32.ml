module type Fmap_Alt_Sig_Example = sig
  type 'a t

  val fmap : ('a -> 'b) -> 'a t -> 'b t
end

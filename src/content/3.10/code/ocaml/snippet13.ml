(* Higher rank types can be introduced via records *)
module NT_as_Ends (F : Functor) (G : Functor) = struct
  type set_of_nt = { nt : 'a. 'a F.t -> 'a G.t }
end

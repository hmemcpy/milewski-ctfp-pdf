(* Here 'a and 'b are (Haskell-like) functorial types due
   to the application of the FU and GU OCaml modules *)
val bimap :
  ('a -> 'a_prime) -> ('b -> 'b_prime) ->
  ('a, 'b) t -> ('a_prime, 'b_prime) t

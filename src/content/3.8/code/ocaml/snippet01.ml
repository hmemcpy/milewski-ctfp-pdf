module type Algebra = functor
  (F : sig
     type 'a f
   end)
  -> sig
  type 'a algebra = 'a F.f -> 'a
end

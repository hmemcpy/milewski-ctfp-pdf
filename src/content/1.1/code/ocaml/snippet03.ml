module Compose_Example
    (F : Polymorphic_Function_F)
    (G : Polymorphic_Function_G with type b = F.b) =
struct
  (** OCaml doesn't have a compose operator. So, creating one. **)
  let ( >> ) g f x = g (f x)

  let compose : 'a -> 'c = G.g >> F.f
end

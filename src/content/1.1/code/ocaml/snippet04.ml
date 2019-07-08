module Compose_Three_GF = functor(F:Polymorphic_Function_F)(G:Polymorphic_Function_G with type b = F.b)(H:Polymorphic_Function_H with type c = G.c) -> struct
  let compose : 'a -> 'd = H.h >> (G.g >> F.f)
end

module Compose_Three_HG = functor(F:Polymorphic_Function_F)(G:Polymorphic_Function_G with type b = F.b)(H:Polymorphic_Function_H with type c = G.c) -> struct
  let compose : 'a -> 'd = (H.h >> G.g) >> F.f
end

Compose_Three_GF.compose = Compose_Three_HG.compose

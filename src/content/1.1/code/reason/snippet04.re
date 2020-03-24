module Compose_Three_GF =
       (
         F: Polymorphic_Function_F,
         G: Polymorphic_Function_G with type b = F.b,
         H: Polymorphic_Function_H with type c = G.c,
       ) => {
  let compose: 'a => 'd = H.h >> (G.g >> F.f);
};

module Compose_Three_HG =
       (
         F: Polymorphic_Function_F,
         G: Polymorphic_Function_G with type b = F.b,
         H: Polymorphic_Function_H with type c = G.c,
       ) => {
  let compose: 'a => 'd = H.h >> G.g >> F.f;
};

Compose_Three_GF.compose == Compose_Three_HG.compose
module FreeFunctorAlt = (F: {type f('a);}) : Functor => {
  module type F = FreeF_Alt with type f('a) = F.f('a);

  type t('a) = (module F with type a = 'a);

  let fmap =
      (type a', type b', f, module FF: F with type a = a')
      : (module F with type a = b') =>
    (module {
       type a = b';
       type f('a) = F.f('a);

       let freeF = bi => FF.freeF(a => bi(f(a)));
    });
};

module FreeFunctor = (F: {type f('a);}) : Functor => {
  module type F = FreeF with type f('a) = F.f('a);

  type t('a) = (module F with type a = 'a);

  let fmap =
    (type a', type b', 
      f: a' => b', module FF: F with type a = a') :
    (module F with type a = b') =>
    (module {
       type f('a) = F.f('a);
       type a = b';
       type i = FF.i;

       let h = i => f(FF.h(i));
       let fi = FF.fi;
    });
};

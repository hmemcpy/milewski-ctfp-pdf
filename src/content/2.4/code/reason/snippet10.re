module NT_Impl = (F: Functor with type t('a) = list('a)): 
    (NT_AX_FX with type a = int and type t('x) = list('x)) => {
  type a = int;
  type t('x) = list('x);
  
  let alpha: 'x . (int => 'x) => list('x) = h => F.fmap(h, [12]);
};

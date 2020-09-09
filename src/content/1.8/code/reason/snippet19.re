module KleisliFunctor: Functor = {
  type t('a) = writer('a);
  
  let fmap = f =>
    KleisliComposition.(>=>)(id, x => KleisliIdentity.return(f(x)));
};

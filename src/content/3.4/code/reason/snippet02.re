module WriterInstance = (W: {type w;}) : 
       (Functor with type t('a) = writer(W.w, 'a)) => {
  type t('a) = writer(W.w, 'a);

  let fmap = (f, Writer(a, w)) => Writer(f(a), w);
};

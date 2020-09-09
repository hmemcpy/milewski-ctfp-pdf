type stream_f('e, 'a) =
  | StreamF(('e, 'a));

module Stream_Functor = (E: {type e;}) : 
       (Functor with type t('a) = stream_f(E.e, 'a)) => {
  type t('a) = stream_f(E.e, 'a);

  let fmap = f =>
    fun
    | StreamF(e, a) => StreamF(e, f(a));
};

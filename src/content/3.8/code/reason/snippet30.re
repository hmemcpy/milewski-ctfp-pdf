module List_C = (E: {type e;}) => {
  module Stream_F: Functor with type t('a) = stream_f(E.e, 'a) =
    Stream_Functor(E);

  module Cata_Stream = Cata(Stream_F);

  let to_list_c: Cata_Stream.fix(list(E.e)) => list(E.e) = (
    s_fix => Cata_Stream.cata((StreamF(e, a)) => [e, ...a], s_fix):
      Cata_Stream.fix(list(E.e)) => list(E.e)
  );
};

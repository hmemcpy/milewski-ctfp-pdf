module Ana = (F: Functor) => {
  type fix('a) =
    | Fix(F.t(fix('a)));

  let rec ana: ('a => F.t('a), 'a) => fix('a) = (
    (coalg, a) => Fix(F.fmap(ana(coalg), coalg(a))):
      ('a => F.t('a), 'a) => fix('a)
  );
};

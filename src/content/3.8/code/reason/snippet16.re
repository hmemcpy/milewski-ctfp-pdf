module Cata = (F: Functor) => {
  type fix('a) =
    | Fix(F.t(fix('a)));

  let fix: F.t(fix('a)) => fix('a) = (
    f => Fix(f): F.t(fix('a)) => fix('a)
  );
  let unfix: fix('a) => F.t(fix('a)) = (
    (Fix(f)) => f: fix('a) => F.t(fix('a))
  );

  let rec cata: (F.t('a) => 'a, fix('a)) => 'a = (
    (alg, fixf) => alg(F.fmap(cata(alg), unfix(fixf))):
      (F.t('a) => 'a, fix('a)) => 'a
  );
};

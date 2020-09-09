module BindUsingFunctionAndJoin = (F: Functor) => {
  type m('a) = F.t('a);

  /** Make the type signature of join work
  without providing an implementation **/
  external join: m(m('a)) => m('a) = "%identity";

  let (>>=) = (ma, f) => join(F.fmap(f, ma));
};

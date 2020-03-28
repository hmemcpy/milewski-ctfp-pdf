module type Monad_Join = (F: Functor) => {
  type m('a) = F.t('a);

  let join: m(m('a)) => m('a);
  let return: 'a => m('a);
};

module type Monad_Bind = {
  type m('a);

  let (>>=): (m('a), 'a => m('b)) => m('b);
  let return: 'a => m('a);
};

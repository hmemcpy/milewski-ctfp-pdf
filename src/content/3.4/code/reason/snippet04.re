module type Monad = {
  type m('a);

  let (>=>): ('a => m('b), 'b => m('c), 'a) => m('c);
  let return: 'a => m('a);
};

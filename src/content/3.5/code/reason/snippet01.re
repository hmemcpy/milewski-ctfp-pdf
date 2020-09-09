module List_Monad: Monad_Join = {
  type m('a) = list('a);

  let join = List.concat;
  let return = a => [a];
};

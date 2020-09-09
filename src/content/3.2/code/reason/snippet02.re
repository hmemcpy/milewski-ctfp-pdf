module type Unit_Example = {
  type m('a);

  let return: 'd => m('d);
};

module type BtoA = {
  type a;
  type b;

  let btoa: b => a;
};

/* Define the Yoneda embedding */
module Yoneda_Embedding = (E: BtoA) => {
  let fromY: 'x. (E.a => 'x, E.b) => 'x = (f, b) => f(E.btoa(b));
};

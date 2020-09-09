let to_exp = (type a', type b', f) :
  (module Exp with type a = a' and type b = b') =>
  (module {
     type a = a';
     type b = b';
     type d('a) =
       | I('a);
     type k('a) = ('a, a);
     type i = unit;

     let fk = ((a, _)) => f(a);
     let di = I();
  });

let from_exp = (type a', type b', 
    module E: Exp with type a = a' and type b = b', a) => {
  let I(i) = E.di;
  E.fk((a, i));
};

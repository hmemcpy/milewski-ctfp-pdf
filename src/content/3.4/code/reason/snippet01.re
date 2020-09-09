/* Depends on OCaml library Core */
module Vlen = (F: Functor with type t('a) = list('a)) => {
  let summable: 
    module Base__.Container_intf.Summable with type t = float =
    (module Float);

  let vlen =
    Float.sqrt
    <.> List.sum(summable, ~f=Fn.id)
    <.> F.fmap(flip(Float.int_pow, 2));
};

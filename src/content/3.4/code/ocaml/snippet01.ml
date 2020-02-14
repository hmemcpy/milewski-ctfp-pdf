(* Depends on OCaml library Core *)
module Vlen (F : Functor with type 'a t = 'a list) = struct
  let summable =
    (module Float : Base__.Container_intf.Summable
      with type t = float)


  let vlen =
    Float.sqrt
    <.> List.sum summable ~f:Fn.id
    <.> F.fmap (flip Float.int_pow 2)
end

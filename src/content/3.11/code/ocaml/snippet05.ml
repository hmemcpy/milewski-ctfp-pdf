module ListMonoid (A : sig
  type a
end) : Monoid with type t = A.a list = struct
  type t = A.a list

  let mempty = []
  let mappend = List.append
end

let fold_map (type i) (module M : Monoid with type t = i) xs f =
  List.fold_left (fun acc a -> M.mappend acc (f a)) M.mempty xs

let to_lst (type x) (xs : x list) =
  let module LM : Monoid with type t = x list = ListMonoid (struct
    type a = x
  end) in
  (module struct
    type a = x
    type m = x list

    module M = LM

    type lst = (a -> LM.t) -> LM.t

    let f g = fold_map (module LM) xs g
  end : Lst
    with type a = x)

let from_lst
    (type x)
    (module LstImpl : Lst with type a = x and type m = x list)
  =
  LstImpl.f (fun x -> [ x ])

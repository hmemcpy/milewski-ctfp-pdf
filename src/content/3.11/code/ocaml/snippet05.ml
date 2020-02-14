let fold_map (type i) (module M : Monoid with type m = i) xs f =
  List.fold_left (fun acc a -> M.mappend acc (f a)) M.mempty xs
;;

let to_lst (type x) (xs : x list) =
  let module LM : Monoid with type m = x list =
    ListMonoid (struct
      type a = x
    end)
  in
  (module struct
    type a = x
    type m = x list

    module M = LM

    type lst = (a -> LM.m) -> LM.m

    let f g = fold_map (module LM) xs g
  end : Lst
    with type a = x)
;;

let from_lst
    (type x)
    (module LstImpl : Lst with type a = x and type m = x list)
  =
  LstImpl.f (fun x -> [ x ])
;;

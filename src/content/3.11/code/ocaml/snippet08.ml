let to_exp (type a' b') f =
  (module struct
    type a = a'
    type b = b'
    type 'a d = I of 'a
    type 'a k = 'a * a
    type i = unit

    let fk (a, _) = f a
    let di = I ()
  end : Exp
    with type a = a'
     and type b = b')
;;

let from_exp
    (type a' b')
    (module E : Exp with type a = a' and type b = b')
    a
  =
  let (I i) = E.di in
  E.fk (a, i)
;;

(* Implement Extract *)
module StreamComonadBase (F : Functor with type 'a t = 'a stream) :
  ComonadBase with type 'a w = 'a stream = struct
  type 'a w = 'a stream

  include F

  let extract (Cons (x, _)) = x
end

(* Implement duplicate *)
module StreamComonadDuplicate :
  ComonadDuplicate with type 'a w = 'a stream = struct
  type 'a w = 'a stream

  let rec duplicate (Cons (x, xs)) =
    Cons (Cons (x, xs), Lazy.from_val (duplicate (Lazy.force xs)))
  ;;
end

(* Generate full Comonad Instance *)
module StreamComonad : Comonad with type 'a w = 'a stream =
  ComonadImplViaExtend
    (StreamComonadBase (StreamFunctor)) (StreamComonadDuplicate)

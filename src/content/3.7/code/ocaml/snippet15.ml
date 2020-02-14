module type ComonadBase = sig
  type 'a w

  include Functor with type 'a t = 'a w

  val extract : 'a w -> 'a
end

module type ComonadDuplicate = sig
  type 'a w

  val duplicate : 'a w -> 'a w w
end

module type ComonadExtend = sig
  type 'a w

  val extend : ('a w -> 'b) -> 'a w -> 'b w
end

module type Comonad = sig
  type 'a w

  include ComonadBase with type 'a w := 'a w
  include ComonadExtend with type 'a w := 'a w
  include ComonadDuplicate with type 'a w := 'a w
end

(* Construct a full comonad instance using one of the following modules *)
module ComonadImplViaExtend : functor
  (C : ComonadBase)
  (D : ComonadDuplicate with type 'a w = 'a C.w)
  -> Comonad with type 'a w = 'a C.w =
functor
  (C : ComonadBase)
  (D : ComonadDuplicate with type 'a w = 'a C.w)
  ->
  struct
    include C
    include D

    let extend f wa = (C.fmap f) (D.duplicate wa)
  end

module ComonadImplViaDuplicate : functor
  (C : ComonadBase)
  (E : ComonadExtend with type 'a w = 'a C.w)
  -> Comonad with type 'a w = 'a C.w =
functor
  (C : ComonadBase)
  (E : ComonadExtend with type 'a w = 'a C.w)
  ->
  struct
    include C
    include E

    let duplicate (wa : 'a w) : 'a w w = E.extend id wa
  end

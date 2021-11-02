(* Putting it all together to show the equivalence between
   unit/counit and left_adjunct/right_adjunct *)
module type Adjunction = functor
  (F : Functor)
  (U : Representable)
  -> sig
  val unit : 'a -> 'a F.t U.t
  val counit : 'a U.t F.t -> 'a
  val left_adjunct : ('a F.t -> 'b) -> 'a -> 'b U.t
  val right_adjunct : ('a -> 'b U.t) -> 'a F.t -> 'b
end

(* Adjunction via unit/counit *)
module type Adjunction_Unit_Counit = functor
  (F : Functor)
  (U : Representable)
  -> sig
  val unit : 'a -> 'a F.t U.t
  val counit : 'a U.t F.t -> 'a
end

(* Adjunction via left and right adjoints *)
module type Adjunction_Hom_Set = functor
  (F : Functor)
  (U : Representable)
  -> sig
  val left_adjunct : ('a F.t -> 'b) -> 'a -> 'b U.t
  val right_adjunct : ('a -> 'b U.t) -> 'a F.t -> 'b
end

(* Implementing unit/counit from left and right adjoint definitions *)
module Adjunction_From_Hom_Set (A : Adjunction_Hom_Set) : Adjunction =
functor
  (F : Functor)
  (U : Representable)
  ->
  struct
    type 't f = 't F.t
    type 't u = 't U.t

    module M = A (F) (U)
    include M

    let unit : 'a. 'a -> 'a f u = fun a -> M.left_adjunct idty a

    let counit : 'a. 'a u f -> 'a =
     fun fua -> M.right_adjunct idty fua
   ;;
  end

(* Implementing left and right adjunct from unit/counit Definitions *)
module Adjunction_From_Unit_Counit (A : Adjunction_Unit_Counit) :
  Adjunction =
functor
  (F : Functor)
  (U : Representable)
  ->
  struct
    type 't f = 't F.t
    type 't u = 't U.t

    module M = A (F) (U)
    include M

    let left_adjunct f a = (U.fmap f) (M.unit a)
    let right_adjunct f fa = M.counit (F.fmap f fa)
  end

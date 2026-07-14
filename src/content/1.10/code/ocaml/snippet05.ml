(* Given a Functor implementation for Option and List,
   the following equality should hold: *)
OptionFunctor.fmap f % safe_head = safe_head % ListFunctor.fmap f

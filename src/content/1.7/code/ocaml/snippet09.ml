module Test_Functor_Compose (F : Functor) = struct
  open F

  let ( % ) = Fun.compose

  let test_compose f g x =
    assert (fmap (f % g) x = fmap f (fmap g x))
end

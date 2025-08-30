toExp :: (a -> b) -> Exp a b
toExp f = Lan (f . fst) (Identity ())

fromExp :: Exp a b -> (a -> b)
fromExp (Lan f (Identity x)) = \a -> f (a, x)

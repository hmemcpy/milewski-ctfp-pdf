class Representable f where
    type Rep f :: *
    tabulate :: (Rep f -> x) -> f x
    index    :: f x -> Rep f -> x
instance Contravariant (Op a) where
    contramap f h = h . f
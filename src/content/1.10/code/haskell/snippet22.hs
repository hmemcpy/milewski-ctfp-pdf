instance Contravariant (Op r) where
    contramap f (Op g) = Op (g . f)
newtype ToString a = ToString (a -> String) 
instance Contravariant ToString where 
    contramap f (ToString g) = ToString (g . f)
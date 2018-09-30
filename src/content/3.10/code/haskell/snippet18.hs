data Procompose q p a b where
    Procompose :: q a c -> p c b -> Procompose q p a b
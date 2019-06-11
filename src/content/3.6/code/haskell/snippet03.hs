class Monoid m where
    mappend :: m -> m -> m
    mempty  :: m
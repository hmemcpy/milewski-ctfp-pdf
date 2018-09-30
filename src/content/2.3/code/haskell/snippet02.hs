instance Monoid [a] where
    mempty = []
    mappend = (++)
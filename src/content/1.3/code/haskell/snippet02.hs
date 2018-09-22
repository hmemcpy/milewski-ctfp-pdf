instance Monoid String where
    mempty = ""
    mappend = (++)
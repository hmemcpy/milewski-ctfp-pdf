instance Monoid w => Monad (Writer w) where
    f >=> g = \a ->
        let Writer (b, s) = f a
            Writer (c, s') = g b
        in Writer (c, s `mappend` s')
    return a = Writer (a, mempty)
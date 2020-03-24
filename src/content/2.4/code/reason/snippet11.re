F.fmap(f, F.fmap(h, [12])) == F.fmap(compose(f, h), [12]);

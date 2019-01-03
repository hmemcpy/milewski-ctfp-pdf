(f >=> g) ==
    (flatten compose fmap[B, T[C]](g) compose f)
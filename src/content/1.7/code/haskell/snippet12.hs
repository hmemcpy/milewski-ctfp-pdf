instance Eq Point where
    (Pt x y) == (Pt x' y') = x == x' && y == y'
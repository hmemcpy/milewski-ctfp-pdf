alpha :: ((a, b), c) -> (a, (b, c))
alpha ((x, y), z) = (x, (y, z))
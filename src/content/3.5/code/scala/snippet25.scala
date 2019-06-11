def flatMap[A, B]: ((A => R) => R) =>
    (A => (B => R) => R) =>
    ((B => R) => R)
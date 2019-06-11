fmap(f)(fmap(h)(List(12))) == fmap(f compose h)(List(12))

// Or using scala stdlib:
List(12).map(h).map(f) == List(12).map(f compose h)
let safe_head = 
  (fmap([x, ...xs])) == safe_head(f([x, ... xs])) == Some(f(x));
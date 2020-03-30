let contramap: ('c_prime => 'c, 'c => 'limD, 'c_prime) => 'limD = (
  (f, u) => compose(u, f): 
    ('c_prime => 'c, 'c => 'limD, 'c_prime) => 'limD
);

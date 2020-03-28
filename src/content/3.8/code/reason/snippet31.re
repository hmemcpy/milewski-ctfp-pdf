/* Gen.t is used to represent infinite data structures like haskell's lazy list */
external unfold: ('b => option(('a, 'b)), 'b) => Gen.t('a) = ;

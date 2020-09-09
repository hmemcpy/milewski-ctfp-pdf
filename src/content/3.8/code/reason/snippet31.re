/* Gen.t is used to represent infinite data structures 
   like haskell's lazy list */
let unfold: ('b => option(('a, 'b)), 'b) => Gen.t('a);

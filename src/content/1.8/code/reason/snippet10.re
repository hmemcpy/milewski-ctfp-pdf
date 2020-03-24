module BiCompBifunctor =
       (
         BF: BifunctorCore, 
         FU: Functor, 
         GU: Functor
        ): BifunctorCore => {
  type t('a, 'b) =
    | BiComp(BF.t(FU.t('a), GU.t('b)));
    
  let bimap = (f, g, BiComp(x)) =>
    BiComp(BF.bimap(FU.fmap(f), GU.fmap(g), x));
};

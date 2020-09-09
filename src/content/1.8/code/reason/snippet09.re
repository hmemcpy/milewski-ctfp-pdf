/** ReasonML doesn't support higher kinded types. 
 * So, we have to use module functors to emulate the behavior higher kinded types. 
 * There's less verbose options using type defunctionalization 
 * but it's more advanced and obscures the flow of this book */
module type BiComp =
  (
    BF: {type t('a, 'b);},
    FU: {type t('a);}, 
    GU: {type t('b);}
  ) => {
    type bicomp('a, 'b) =
      | BiComp(BF.t(FU.t('a), GU.t('b)));
  };

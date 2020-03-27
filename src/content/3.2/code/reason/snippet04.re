/* L is Functor F and R is Representable Functor U */
module type Adjunction =
  (F: Functor, U: Representable) => {
    let unit: 'a => U.t(F.t('a));
    let counit: F.t(U.t('a)) => 'a;
  };

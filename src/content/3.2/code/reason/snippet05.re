module type Adjunction_HomSet =
  (F: Functor, U: Representable) => {
    let left_adjunct: (F.t('a) => 'b, 'a) => U.t('b);
    let right_adjunct: ('a => U.t('b), F.t('a)) => 'b;
  };

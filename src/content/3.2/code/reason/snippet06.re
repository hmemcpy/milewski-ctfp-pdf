/* Putting it all together to show the equivalence between 
* unit & counit and left_adjunct & right_adjunct */
module type Adjunction =
  (F: Functor, U: Representable) => {
    let unit: 'a => U.t(F.t('a));
    let counit: F.t(U.t('a)) => 'a;
    let left_adjunct: (F.t('a) => 'b, 'a) => U.t('b);
    let right_adjunct: ('a => U.t('b), F.t('a)) => 'b;
  };

/* Adjunction via unit & counit */
module type Adjunction_Unit_Counit =
  (F: Functor, U: Representable) => {
    let unit: 'a => U.t(F.t('a));
    let counit: F.t(U.t('a)) => 'a;
  };

/* Adjunction via left and right adjoints */
module type Adjunction_Hom_Set =
  (F: Functor, U: Representable) => {
    let left_adjunct: (F.t('a) => 'b, 'a) => U.t('b);
    let right_adjunct: ('a => U.t('b), F.t('a)) => 'b;
  };

/* Implementing unit & counit from left and right adjoint definitions */
module Adjunction_From_Hom_Set = (A: Adjunction_Hom_Set) : Adjunction =>
  (F: Functor, U: Representable) => {
    type f('t) = F.t('t);
    type u('t) = U.t('t);

    module M = A(F, U);
    include M;

    let unit: 'a. 'a => u(f('a)) = a => M.left_adjunct(idty, a);
    let counit: 'a. f(u('a)) => 'a = fua => M.right_adjunct(idty, fua);
  };

/* Implementing left and right adjunct from unit & counit Definitions */
module Adjunction_From_Unit_Counit = (A: Adjunction_Unit_Counit) : Adjunction =>
  (F: Functor, U: Representable) => {
    type f('t) = F.t('t);
    type u('t) = U.t('t);

    module M = A(F, U);
    include M;

    let left_adjunct = (f, a) => (U.fmap(f))(M.unit(a));
    let right_adjunct = (f, fa) => M.counit(F.fmap(f, fa));
  };

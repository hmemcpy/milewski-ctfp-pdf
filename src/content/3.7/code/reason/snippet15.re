module type ComonadBase = {
  type w('a);

  include Functor with type t('a) = w('a);

  let extract: w('a) => 'a;
};

module type ComonadDuplicate = {
  type w('a);

  let duplicate: w('a) => w(w('a));
};

module type ComonadExtend = {
  type w('a);

  let extend: (w('a) => 'b, w('a)) => w('b);
};

module type Comonad = {
  type w('a);

  include ComonadBase with type w('a) := w('a);
  include ComonadExtend with type w('a) := w('a);
  include ComonadDuplicate with type w('a) := w('a);
};

/* Construct a full comonad instance using one of the 
* following modules */
module ComonadImplViaExtend:
  (C: ComonadBase, D: ComonadDuplicate with type w('a) = C.w('a)) =>
   Comonad with type w('a) = C.w('a) =
  (C: ComonadBase, D: ComonadDuplicate with type w('a) = C.w('a)) => {
    include C;
    include D;

    let extend = (f, wa) => (C.fmap(f))(D.duplicate(wa));
  };

module ComonadImplViaDuplicate:
  (C: ComonadBase, E: ComonadExtend with type w('a) = C.w('a)) =>
   Comonad with type w('a) = C.w('a) =
  (C: ComonadBase, E: ComonadExtend with type w('a) = C.w('a)) => {
    include C;
    include E;

    let duplicate = (wa: w('a)): w(w('a)) => E.extend(id, wa);
  };

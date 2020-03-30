/** You can represent bifunctor defintion in two forms
 * and implement just and derive the other from it. */
module type BifunctorCore = {
  type t('a, 'b);

  let bimap: ('a => 'c, 'b => 'd, t('a, 'b)) => t('c, 'd);
};

module type BifunctorExt = {
  type t('a, 'b);

  let first: ('a => 'c, t('a, 'b)) => t('c, 'b);
  let second: ('b => 'd, t('a, 'b)) => t('a, 'd);
};

module BifunctorCore_Using_Ext = (M: BifunctorExt) : BifunctorCore => {
  type t('a, 'b) = M.t('a, 'b);

  let bimap = (g, h, x) => M.first(g, M.second(h, x));
};

module BifunctorExt_Using_Core = (M: BifunctorCore) : BifunctorExt => {
  type t('a, 'b) = M.t('a, 'b);
  
  let first = (g, x) => M.bimap(g, id, x);
  let second = (h, x) => M.bimap(id, h, x);
};

/* Profunctor definition */
module type Profunctor = {
  type p('a, 'b);

  let dimap: ('a => 'b, 'c => 'd, p('b, 'c)) => p('a, 'd);
};

/* Profunctor alternate definition */
module type ProfunctorExt = {
  type p('a, 'b);

  let lmap: ('a => 'b, p('b, 'c)) => p('a, 'c);
  let rmap: ('b => 'c, p('a, 'b)) => p('a, 'c);
};

/* Profunctor dimap defined using lmap and rmap */
module Profunctor_Using_Ext = (PF: ProfunctorExt) : Profunctor => {
  type p('a, 'b) = PF.p('a, 'b);

  let dimap = (f, g) => compose(PF.lmap(f), PF.rmap(g));
};

/** Profunctor lmap and rmap defined using dimap */
module ProfunctorExt_Using_Dimap = (PF: Profunctor) : ProfunctorExt => {
  type p('a, 'b) = PF.p('a, 'b);
  
  let lmap = f => PF.dimap(f, id);
  let rmap = g => PF.dimap(id, g);
};

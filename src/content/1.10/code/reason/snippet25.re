module Op_Bool = Op_Contravariant({type r = bool;});

let op_bool_contramap: ('b => 'a, Op_Bool.t('a)) => Op_Bool.t('b) = (
  Op_Bool.contramap: ('b => 'a, Op_Bool.t('a)) => Op_Bool.t('b)
);

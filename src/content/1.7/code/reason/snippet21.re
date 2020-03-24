module type T = {type t;};

module Partially_Applied_FunctionType = (T: T) => {
  type t('b) = T.t => 'b;
};

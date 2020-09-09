module PartialArrow = (T: {type r;}) => {
  type t('a) = T.r => 'a;
};

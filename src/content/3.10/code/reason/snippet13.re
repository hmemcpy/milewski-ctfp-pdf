/* Higher rank types can be introduced via records */
module NT_as_Ends = (F: Functor, G: Functor) => {
  type set_of_nt = {nt: 'a. F.t('a) => G.t('a)};
};

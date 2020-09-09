/* There is no compose operator in ReasonML */
compose(dimap(id, f), alpha) == compose(dimap(f, id), alpha);

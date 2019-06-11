tell :: w -> Writer w ()
tell s = Writer ((), s)
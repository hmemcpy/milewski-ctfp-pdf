module Stream_Int = Stream_Functor({type e = int;});

module Ana_Stream = Ana(Stream_Int);

/* The fixpoint translated to ReasonML is eager in its evaluation.
   Hence, executing the following function will cause overflow.
   So, wrapping it inside a lazy */
let primes = lazy(Ana_Stream.ana(era, Gen.init(i => i + 2)));

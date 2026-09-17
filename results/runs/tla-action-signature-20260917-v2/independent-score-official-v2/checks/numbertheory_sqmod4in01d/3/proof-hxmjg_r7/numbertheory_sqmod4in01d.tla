----- MODULE numbertheory_sqmod4in01d -----
EXTENDS Integers, TLAPS

THEOREM numbertheory_sqmod4in01d ==
  \A a \in Int : ((a * a) % 4 = 0) \/ ((a * a) % 4 = 1)BY NoSetContainsEverything
============================================================================================

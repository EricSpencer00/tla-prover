----- MODULE numbertheory_sqmod3in01d -----
EXTENDS Integers, TLAPS

THEOREM numbertheory_sqmod3in01d ==
    \A a \in Int : (a * a % 3 = 0) \/ (a * a % 3 = 1)BY NoSetContainsEverything
=============================================================================================

----- MODULE numbertheory_x5neqy2p4 -----
EXTENDS Integers, TLAPS

THEOREM numbertheory_x5neqy2p4 ==
    \A x, y \in Int :
        (x * x * x * x * x) # (y * y + 4)BY NoSetContainsEverything
=============================================================================================

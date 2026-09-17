---------------------------- MODULE mathd_numbertheory_412 ---------------------------
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_412 ==
    \A x, y \in Int :
        (x % 19 = 4) /\ (y % 19 = 7) =>
        ((x + 1) * (x + 1) * (y + 5) * (y + 5) * (y + 5)) % 19 = 13
BY SMT, SetExtensionality, NoSetContainsEverything
=============================================================================

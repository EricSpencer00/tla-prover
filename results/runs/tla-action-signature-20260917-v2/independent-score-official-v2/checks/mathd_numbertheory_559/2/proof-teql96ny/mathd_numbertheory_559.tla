----- MODULE mathd_numbertheory_559 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_559 ==
    \A x, y \in Nat :
        (x % 3 = 2) /\ (y % 5 = 4) /\ (x % 10 = y % 10)
        => 14 <= xBY SMT, SetExtensionality
====

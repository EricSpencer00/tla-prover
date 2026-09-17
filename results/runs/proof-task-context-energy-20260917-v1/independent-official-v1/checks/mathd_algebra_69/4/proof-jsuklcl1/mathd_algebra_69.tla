----- MODULE mathd_algebra_69 -----
EXTENDS TLAPS, Integers

THEOREM mathd_algebra_69 ==
    \A rows, seats \in Nat :
        (rows * seats = 450) /\ ((rows + 5) * (seats - 3) = 450) => rows = 25BY SMT, SetExtensionality
=============================================================================

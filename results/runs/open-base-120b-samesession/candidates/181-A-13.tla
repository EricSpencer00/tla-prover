---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == \A n \in NatOverride : ((2 * n) % 2 = 0)

PROPERTIES == INVARIANTS
====
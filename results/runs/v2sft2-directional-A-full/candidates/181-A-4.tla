---- MODULE MC_sums_even ----
EXTENDS SumsEven

CONSTANT MaxNat, Nat

VARIABLE dummy

Init == dummy = 0
Next == dummy' = dummy
Spec == Init /\ [][Next]_<<dummy>>

SPECIFICATION == Spec
INVARIANTS == {}
PROPERTIES == {}

====
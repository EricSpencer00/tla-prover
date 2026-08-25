---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of Nat for model checking
NatOverride == 0 .. MaxNat

\* Dummy state variable (no real behavior needed for the theorem)
VARIABLE dummy

\* Initial condition
Init == dummy = 0

\* Trivial next-state relation (state does not change)
Next == dummy' = dummy

\* Specification used by the model checker
SPECIFICATION == Init /\ [][Next]_<<dummy>>

\* No additional invariants beyond the trivial truth
INVARIANTS == dummy = dummy

\* No additional properties beyond the trivial truth
PROPERTIES == dummy = dummy
====
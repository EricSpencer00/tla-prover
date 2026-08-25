---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Dummy state variable (no real state needed for the theorem)
VARIABLE dummy

Init == dummy = 0
Next == dummy' = dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>
INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == TRUE
====
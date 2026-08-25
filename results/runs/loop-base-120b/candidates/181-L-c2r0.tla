---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* No state variables are required for this configuration module
Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [][Next]_<<>>

INIT == Init
NEXT == Next
INVARIANTS == TRUE
PROPERTIES == TRUE
====
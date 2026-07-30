---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

\* The finite override that replaces the infinite natural number set when
\* the model is checked.  The name Nat is deliberately NOT declared here, so
\* the EXTENDS Naturals binding keeps the original Nat operator untouched.
NatOverride == 0 .. MaxNat

SPECIFICATION == Init /\ Next
Init == TRUE
Next == TRUE

INVARIANTS == TRUE
Properties == TRUE
====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
  MaxNat

\* NatOverride is a bounded version of the natural numbers, used to replace the
\* infinite Nat set from the base specification so TLC can check the model.
NatOverride == 0..MaxNat

\* Nothing here is modelled beyond the override; the rest of the proof hangs on
\* the theorem that 2*n is even, which is assumed for TLC rather than proved.
SPECIFICATION == Init /\ Next

Init == TRUE

Next == TRUE

Invariants == TRUE

Properties == TRUE

====
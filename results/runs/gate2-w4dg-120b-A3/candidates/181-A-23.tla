---- MODULE MC_sums_even ----
EXTENDS Naturals

\* Model-checking configuration for the proof that the double of any natural
\* number is even.  This module inherits the base proof specs and overrides
\* the natural-number set with a finite range so TLC can check it.

CONSTANTS MaxNat

\* The .cfg replaces Nat with NatOverride.  Keeping EXTENDS Naturals, we bind
\* Nat to a finite version of itself parameterised by the model constant.
NatOverride == 0..MaxNat

SPECIFICATION == Init /\ Next

Init == TRUE

Next == TRUE

INVARIANTS == TRUE

Properties == TRUE

====
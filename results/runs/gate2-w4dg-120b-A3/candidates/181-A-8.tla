---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The .cfg file replaces the infinite natural number set with a bounded finite set for
\* model checking. NatOverride is the name the config expects on the left-hand side;
\* the operator on the right (which we define) must be a FINITE version of the natural
\* numbers, so TLC can process the model. EXTENDS Naturals is still in force, but we
\* do not redeclare Nat itself -- the config never asks us to.
NatOverride == 0..MaxNat

SPECIFICATION == Init /\ Next

Init == TRUE

Next == TRUE

INVARIANTS == TRUE

PROPERTIES == TRUE

====
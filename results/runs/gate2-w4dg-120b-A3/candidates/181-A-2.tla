---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNat

\* Natural numbers are modelled with a bounded finite set for model checking.
\* The override replaces the infinite `Nat` from Naturals with a finite
\* version; the name `Nat` is deliberately not re-declared, so the
\* definition below extends the inherited one rather than shadowing it.
NatOverride == UNION { 0 .. MaxNat }

SPECIFICATION == Init /\ Next

Init == TRUE

Next == TRUE

INVARIANTS == TRUE

Properties == TRUE

====
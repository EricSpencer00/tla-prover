---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS MaxNat, Nat

\* ----------------------------------------------------------------------
\* The finite set of natural numbers used for model checking
\* ----------------------------------------------------------------------
NatSet == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Base specification: the theorem that the double of any natural number is even
\* ----------------------------------------------------------------------
DoubleEven == \A n \in NatSet : (2 * n) % 2 = 0

\* ----------------------------------------------------------------------
\* Place-holder state variable (required for TLC to have a state)
\* The actual system has no dynamic behavior; the variable never changes.
\* ----------------------------------------------------------------------
VARIABLE dummy

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == dummy = 0

\* ----------------------------------------------------------------------
\* Stuttering next-state relation (no state change)
\* ----------------------------------------------------------------------
Next == dummy' = dummy

\* ----------------------------------------------------------------------
\* Specification (temporal formula)
\* ----------------------------------------------------------------------
Specification == Init /\ [][Next]_<<dummy>>

\* ----------------------------------------------------------------------
\* Safety property: the theorem that the double of any natural number is even
\* ----------------------------------------------------------------------
Invariant == DoubleEven

\* ----------------------------------------------------------------------
\* Property name required by the .cfg (maps to the same invariant)
\* ----------------------------------------------------------------------
Property == DoubleEven

=============================================================================
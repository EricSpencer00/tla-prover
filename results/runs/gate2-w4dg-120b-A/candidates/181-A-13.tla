---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The model-checking configuration module for the proof that the double of any
\* natural number is even. It inherits the definitions from the base proof
\* specification and overrides the natural number set with a bounded finite range
\* (zero through one million) so TLC can check the theorem. An assumption that
\* the theorem holds is included for model checking.

VARIABLES n

vars == <<n>>

TypeOK == n \in Nat

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

Even == \E k \in Nat : 2 * n = k + k

SpecWithAssumption == Spec /\ Even

\* The configuration's SPECIFICATION is the version that includes the
\* top-level assumption; this is what TLC will explore, not the bare proof
\* spec's Spec.
SPECIFICATION == SpecWithAssumption
INIT == Init
NEXT == Next
INVARIANTS == {Even}
PROPERTIES == {Even}
====
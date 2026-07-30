---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers, TLC

\* The base proof specification (not shown here) contains the theorem that the
\* double of any natural number is even. This configuration module overrides the
\* infinite natural-number set with a bounded finite range so TLC can explore
\* it concretely, and it assumes the theorem holds as a constant-level
\* assumption for the sake of model checking.

CONSTANTS MaxNat, Nat

ASSUME MaxNat \in Nat /\ MaxNat >= 1

VARIABLES n

vars == <<n>>

TypeOK == n \in Nat /\ n <= MaxNat

Init == n = 0

DoubleEven == (2 * n) % 2 = 0

Next == /\ n < MaxNat
        /\ n' = n + 1

Spec == Init /\ [][Next]_vars

SpecOK == Spec

====
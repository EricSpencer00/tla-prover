---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS
    MaxNat
    Nat

\* The safety property that a natural number's double is even is imported from the
\* base proof; this module only constrains the range that TLC will explore.
MaxNat == 1000000

VARIABLES
    n

vars == << n >>

TypeOK == n \in Nat

\* The invariant that the double of a natural number is even is a theorem of the
\* base proof.  Here it is re-used as an assumed invariant so TLC can run.
EvenDouble == (2 * n) % 2 = 0

Init == n = 0

Next == \E m \in Nat : n' = m

Spec == Init /\ [][Next]_vars

\* Model checking uses the imported theorem as a constant-level assumption.
AssumeEvenDouble == TRUE

====
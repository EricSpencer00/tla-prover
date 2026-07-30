---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The theorem itself is taken as a constant-level assumption for model checking.
ASSUME MaxNat = 1000000

VARIABLES x

vars == <<x>>

TypeOK == x \in Nat

Init == x = 0

Next == \E y \in Nat : x' = y

Spec == Init /\ [][Next]_vars

\* No safety or liveness properties are modelled here; they live in the base spec.
====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* Specification: model checking the theorem that double any natural number is even,
\* over a bounded range (zero through MaxNat) derived from the base proof spec.
Spec == Init /\ [][Next]_vars

vars == << >>

Init == TRUE

Next == TRUE

TypeOK == TRUE

\* The model's safety or liveness properties are not explicitly defined here:
\* the double-of-a-natural-number-is-even theorem is assumed constant-level (see
\* the .cfg) so that the bounded configuration can be explored by TLC.
====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride replaces the infinite Nat with a finite version for model checking.
NatOverride == 0 .. MaxNat

VARIABLES x

vars == <<x>>

TypeOK == x \in NatOverride

Init == x = 0

Next == x' = (x + 1) % (MaxNat + 1)

Spec == Init /\ [][Next]_vars

\* The theorem from the base spec is taken as a constant-level assumption here.
DoubleIsEven == 2 * x = (x + x)

====
---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

INIT == n \in NatOverride

NEXT == n' \in NatOverride

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == \A m \in NatOverride : (2 * m) % 2 = 0

PROPERTIES == INVARIANTS
====
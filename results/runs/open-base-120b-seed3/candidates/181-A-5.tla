---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers, to be used by the .cfg to replace Nat *)
NatOverride == 0 .. MaxNat

VARIABLE n

Even(x) == x % 2 = 0

INIT == n \in NatOverride

NEXT == UNCHANGED n

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == \A m \in NatOverride : Even(2 * m)

PROPERTIES == \A m \in NatOverride : Even(2 * m)

====
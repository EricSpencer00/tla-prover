---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

IsEven(x) == x % 2 = 0

INIT == n \in NatOverride

NEXT == n' = (n + 1) % (MaxNat + 1)

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

INVARIANTS == IsEven(2 * n)

PROPERTIES == \A m \in NatOverride : IsEven(2 * m)

====
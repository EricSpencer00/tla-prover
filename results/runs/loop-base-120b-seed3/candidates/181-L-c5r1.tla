---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

IsEven(x) == x % 2 = 0

Init == n \in NatOverride

Next == n' = (n + 1) % (MaxNat + 1)

Spec == Init /\ [][Next]_<<n>>

Invariant == IsEven(2 * n)

Theorem == \A m \in NatOverride : IsEven(2 * m)

====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

\* The bounded natural-number set for model checking.
CONSTANTS = {MaxNat, Nat}

VARIABLES n

vars == <<n>>

TypeInvariant == n \in Nat

Init == n = 0

Next == \E y \in Nat : n' = y

NextLHS == \E y \in Nat : n' = y

Spec == Init /\ [][Next]_vars

InitLHS == Init

NextLHSSpec == InitLHS /\ [][NextLHS]_vars

Even(x) == \E y \in Nat : x = 2 * y

SumIsEven == Even(n)

====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(*--- Finite version of Nat ---*)
NatOverride == 0 .. MaxNat

VARIABLE n

(*--- Initial state ---*)
INIT == n = 0

(*--- Next-state relation ---*)
NEXT == /\ n \in NatOverride
        /\ n' = n + 1
        /\ n' \in NatOverride

(*--- Specification ---*)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(*--- Helper definition for evenness ---*)
Even(x) == x % 2 = 0

(*--- Invariant that the double of n is even ---*)
Invariant == Even(2 * n)

INVARIANTS == Invariant

(*--- Property asserting the theorem for all numbers in the finite range ---*)
PROPERTIES == \A m \in NatOverride : Even(2 * m)

====
---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(*--- Finite version of Nat, used instead of the infinite Nat ---*)
NatOverride == 0 .. MaxNat

VARIABLE n

(*--- Initial predicate ---*)
INIT == n \in NatOverride

(*--- Next-state relation (no state change) ---*)
NEXT == UNCHANGED n

(*--- Overall specification ---*)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(*--- Helper definition: evenness within the finite range ---*)
Even(x) == \E k \in NatOverride : x = 2 * k

(*--- Assumed theorem: double of any natural number is even ---*)
THEOREM == \A m \in NatOverride : Even(2 * m)

INVARIANTS == THEOREM

PROPERTIES == THEOREM
====
---- MODULE MC_sums_even ----
EXTENDS Naturals, FiniteSets

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Predicate that a number is even using the finite NatOverride *)
Even(x) == \E k \in NatOverride : x = 2 * k

VARIABLES n

(* Initial state: n is any natural number in the finite range *)
Init == n \in NatOverride

(* Next-state relation: n can become any natural number in the finite range *)
Next == n' \in NatOverride

(* Full specification: init state and always‑enabled next action *)
Spec == Init /\ [][Next]_n

(* Invariant stating that doubling any reachable n yields an even number *)
Inv == Even(2 * n)

INVARIANTS == Inv
PROPERTIES == Inv
====
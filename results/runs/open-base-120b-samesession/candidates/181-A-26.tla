---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE n

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

(* Evenness predicate using the finite NatOverride *)
Even(m) == \E k \in NatOverride : m = 2 * k

(* Initial state: n ranges over the finite natural numbers *)
INIT == n \in NatOverride

(* Next-state relation: n may nondeterministically take any finite natural value *)
NEXT == n' \in NatOverride

(* Full specification combining init and next *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant stating that double of n is even *)
INVARIANTS == Even(2 * n)

(* Property (same as invariant for this simple model) *)
PROPERTIES == Even(2 * n)

====
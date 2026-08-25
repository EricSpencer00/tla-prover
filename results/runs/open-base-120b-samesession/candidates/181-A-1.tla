---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Evenness predicate using the finite NatOverride *)
Even(x) == \E k \in NatOverride : x = 2 * k

(* Initial state: n is any natural number in the bounded range *)
INIT == n \in NatOverride

(* Next-state relation: n can nondeterministically take any value in the bounded range *)
NEXT == n' \in NatOverride

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant expressing that the double of any natural number is even *)
INVARIANTS == \A m \in NatOverride : Even(2 * m)

(* Property (theorem) to be checked by TLC *)
PROPERTIES == \A m \in NatOverride : Even(2 * m)

====
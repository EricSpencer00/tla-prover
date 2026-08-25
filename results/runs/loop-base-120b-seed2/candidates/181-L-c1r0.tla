---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite override for the infinite set Nat *)
NatOverride == 0 .. MaxNat

VARIABLES n

(* Evenness predicate using the finite NatOverride *)
Even(x) == \E y \in NatOverride : x = 2 * y

(* Assumed theorem: the double of any natural number is even *)
Theorem == \A m \in NatOverride : Even(2 * m)

(* Initial state: n is any natural number within the bounded range *)
Init == n \in NatOverride

(* Next-state relation: n steps through the bounded range *)
Next == /\ n' \in NatOverride
        /\ n' = n + 1

(* Overall specification *)
SPECIFICATION == Init /\ [][Next]_<<n>>

(* Invariants to be checked by TLC *)
INVARIANTS == << Theorem >>

(* Temporal properties to be checked by TLC *)
PROPERTIES == << Theorem >>

====
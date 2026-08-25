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

(* Initial state: start at the lower bound of the finite range *)
Init == n = 0

(* Next-state relation: step forward while staying within the bounded range;
   allow stuttering at the upper bound to avoid deadlock. *)
Next == /\ n' \in NatOverride
        /\ IF n < MaxNat THEN n' = n + 1 ELSE n' = n

(* Overall specification *)
SPECIFICATION == Init /\ [][Next]_n

====
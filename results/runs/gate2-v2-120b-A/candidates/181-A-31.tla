---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat
Nat == 0 .. MaxNat

VARIABLE n

(* Initial state: pick any natural number in Nat *)
Init == n \in Nat

(* Action: nondeterministically pick a new value for n within Nat *)
Next == n' \in Nat

(* Safety invariant: the double of the current number is even *)
EvenDouble == (2 * n) % 2 = 0

(* The specification consists of the initial predicate and the next-step action *)
Spec == Init /\ [][Next]_<<n>>

=============================================================================
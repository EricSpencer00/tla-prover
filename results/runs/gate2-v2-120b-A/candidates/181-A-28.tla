---- MODULE MC_sums_even ----
EXTENDS Naturals, TLC

CONSTANT MaxNat, Nat

VARIABLE n

(* The invariant that the double of any natural number is even. *)
EvenDoubles == \A m \in Nat : (2 * m) % 2 = 0

(* Initial state: choose any number from the bounded set. *)
Init == n \in Nat

(* No state changes; the system is static. *)
Next == UNCHANGED n

Spec == Init /\ [][Next]_<<n>>

INIT == Init
NEXT == Next
INVARIANTS == EvenDoubles
PROPERTIES == EvenDoubles

=============================================================================
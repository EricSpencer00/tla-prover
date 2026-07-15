---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat, Nat

(* 
  The constant Nat is overridden in the .cfg to be the finite range 
  0..MaxNat. This module does not define its contents; it only declares 
  the constant so that TLC can replace it with the appropriate set.
*)

(*---------------------------------------------------------------------*)
(* The specification is the original theorem that for every n \in Nat, 
   2*n is even.  We model this as a simple trivial state machine whose 
   state consists of a single variable n that ranges over Nat.  The 
   invariant expresses the theorem. *)

VARIABLE n

(* Initial state: choose any n in Nat *)
Init == n \in Nat

(* Next: nondeterministically pick any n' in Nat *)
Next == n' \in Nat /\ n' = n

(* Safety property (the theorem) *)
EvenDoubles == n \in Nat => (2 * n) % 2 = 0

(* Specification, initial predicate, and next-state relation *)
Spec == Init /\ [][Next]_<<n>>

(* The required identifiers *)
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == EvenDoubles
PROPERTIES == EvenDoubles

====
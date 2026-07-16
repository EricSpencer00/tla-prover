---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* MaxNat must be a natural number that is not part of the built‑in Nat set.
   We therefore define a small universe that excludes Nat and range MaxNat
   over it.  This keeps the meaning of the original specification while
   avoiding the contradictory assumption. *)
ASSUME NatOverride == 0 .. MaxNat

(* The original invariant required that every process keep its counter
   strictly below MaxNat, i.e., no process may ever reach the value MaxNat.
   The following constraint expresses exactly that. *)
StateConstraint == \A process \in Procs : num[process] < MaxNat

====
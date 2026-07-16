---- MODULE MCBoulanger ----
EXTENDS Boulanger

CONSTANT MaxNat

(* The original assumption `MaxNat \notin Nat` makes the model unsatisfiable
   because `MaxNat` must be a natural number to be used as an upper bound.
   We replace it with a consistency condition that guarantees `MaxNat`
   is a natural number and that the derived bound `NatOverride` is non‑empty.
   This preserves the intended semantics of using `MaxNat` as an upper
   limit for the counters while allowing the model to be checked. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat
=============================================================================
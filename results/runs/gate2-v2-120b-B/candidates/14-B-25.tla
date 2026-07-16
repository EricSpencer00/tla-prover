---- MODULE MCBoulanger ----
EXTENDS Boulanger

(* The original specification assumed MaxNat is not a natural number,
   which makes the model inconsistent because NatOverride (= 0..MaxNat)
   would be an empty interval and the state constraint could never hold.
   We replace the assumption with a consistent one that keeps the intended
   semantics: MaxNat must be a natural number (so the bounded set NatOverride
   is well‑defined) and it must be strictly greater than every value of the
   variable num used in the state constraint. This preserves the original
   intention that MaxNat bounds the counters, while allowing TLC to find
   reachable states. *)

CONSTANT MaxNat

ASSUME MaxNat \in Nat
ASSUME MaxNat > 0

NatOverride == 0 .. MaxNat

StateConstraint == \A process \in Procs : num[process] < MaxNat

=============================================================================
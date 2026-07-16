---- MODULE MCBoulanger ----
EXTENDS Boulanger
CONSTANT MaxNat

(* The original assumption \A process \in Procs : num[process] < MaxNat is false
   because the initial state may already violate it.  We replace it with the
   correct safety invariant that the model checker will use to verify that
   the bound is never exceeded during execution.  This preserves the intended
   semantics without weakening the specification. *)
Invariant == \A process \in Procs : num[process] < MaxNat

====
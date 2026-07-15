---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES dummy

(* The dummy variable is never used; it merely gives the spec a state variable. *)

(* ---------------------------------------------------------------------- *)
(*  Init and Next (trivial actions)                                       *)
(* ---------------------------------------------------------------------- *)

Init == dummy = 1

Next == UNCHANGED dummy

(* ---------------------------------------------------------------------- *)
(*  Convenience predicates (required by the task description)            *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<dummy>>

=============================================================================
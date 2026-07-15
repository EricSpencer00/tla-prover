---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*   Backend configuration constants for TLAPS (used only for completeness) *)
(***************************************************************************)

VARIABLES dummy

(* No state variables are specified in the natural-language description, but
   a variable must be declared for the spec to be syntactically well‑formed. *)
Init == dummy = 0

(* No actions are specified, so the stuttering step is the only possible action. *)
Next == UNCHANGED dummy

(* The top‑level specification: start in Init and forever take steps of Next. *)
Spec == Init /\ [][Next]_<<dummy>>

(***************************************************************************)
(*   Fundamental theorems from the description                               *)
(***************************************************************************)

(* Set extensionality: two sets are equal iff they have the same elements. *)
Extensionality == \A X, Y \in SUBSET Nat :
                      ( \A z \in Nat : (z \in X) <=> (z \in Y) ) => X = Y

(* No set contains every possible value (over the natural numbers in this module). *)
NoUniversalSet == \A X \in SUBSET Nat : ~(\A z \in Nat : z \in X)

(***************************************************************************)
(*   Exported operators required by the reference configuration                *)
(***************************************************************************)

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

=============================================================================
---- MODULE TLAPS ----
EXTENDS Naturals, TLC

(* ----------------------------------------------------------------------
   TLAPS backend configuration and fundamental proof-theoretic theorems.
   This module contains no state variables; it merely defines the
   operators required by the configuration and states two basic set
   theorems used throughout the proof library.
   ---------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------
   Trivial initialization and next-state relation.
   Since the specification has no state, both are simply TRUE.
   ---------------------------------------------------------------------- *)
Init == TRUE
Next == TRUE

(* ----------------------------------------------------------------------
   Operators required by the .cfg file (even though they are not used
   elsewhere in this module).
   ---------------------------------------------------------------------- *)
SPECIFICATION == Init /\ [] [Next]_<<>>
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

(* ----------------------------------------------------------------------
   Fundamental theorems
   ---------------------------------------------------------------------- *)

THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S : ~(\A x : x \in S)

====
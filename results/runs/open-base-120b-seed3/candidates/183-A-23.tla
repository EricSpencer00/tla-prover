---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences, TLC, Temporal

(*--------------------------------------------------------------------
  This helper module defines backend pragmas for TLAPS and reserves
  names of temporal‑logic proof rules.  It also states two foundational
  theorems about sets.
--------------------------------------------------------------------*)

VARIABLES dummy

(* Trivial state definition – the module does not model any concrete
   system behavior; the definitions exist only to provide the required
   identifiers. *)
Init == dummy = 0
Next == dummy' = dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

(*--------------------------------------------------------------------
  Fundamental theorems
--------------------------------------------------------------------*)

THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) = (x \in T)) => S = T

THEOREM NoSetContainsAllValues ==
  \A S : \E x : x \notin S

(*--------------------------------------------------------------------
  Reserved names for temporal‑logic proof rules (placeholders)
--------------------------------------------------------------------*)

InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

====
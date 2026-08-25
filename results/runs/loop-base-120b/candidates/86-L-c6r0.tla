---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  No state variables are needed for this configuration module.
--------------------------------------------------------------------*)

(*--------------------------------------------------------------
  Basic specification components required by the task.
--------------------------------------------------------------*)
Init == TRUE

Next == TRUE

SPECIFICATION == Init /\ [][Next]_<<>>

INVARIANTS == {}

PROPERTIES == {}

(*--------------------------------------------------------------
  Foundational theorems required by the description.
--------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) \equiv (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : ~(\A x : x \in S)

(*--------------------------------------------------------------
  Place‑holder definitions for temporal‑logic proof rules.
  These names are reserved to avoid clashes in future modules.
--------------------------------------------------------------*)
InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

====
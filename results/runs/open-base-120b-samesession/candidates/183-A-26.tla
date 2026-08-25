---- MODULE TLAPS ----
EXTENDS FiniteSets

(* No state variables defined *)

Init == TRUE
Next == TRUE

SPECIFICATION == Init /\ [] [Next]_<<>>

INVARIANTS == {}
PROPERTIES == {}

(* Temporal‑logic proof‑rule placeholders – names are reserved *)
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

(* Fundamental theorems *)

THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====
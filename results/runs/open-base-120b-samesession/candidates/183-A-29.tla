---- MODULE TLAPS ----
EXTENDS Naturals, TLC

(*-----------------------------------------------------------------
  Backend prover configurations (placeholders for TLAPS pragmas)
-----------------------------------------------------------------*)
Zenon   == [ "name" |-> "Zenon",   "timeout" |-> 30 ]
Isabelle== [ "name" |-> "Isabelle","timeout" |-> 30 ]
CVC3    == [ "name" |-> "CVC3",    "timeout" |-> 30 ]
Yices   == [ "name" |-> "Yices",   "timeout" |-> 30 ]
VeriT   == [ "name" |-> "VeriT",   "timeout" |-> 30 ]
Z3      == [ "name" |-> "Z3",      "timeout" |-> 30 ]
SPASS   == [ "name" |-> "SPASS",   "timeout" |-> 30 ]
LS4     == [ "name" |-> "LS4",     "timeout" |-> 30 ]

(*-----------------------------------------------------------------
  Temporal‑logic proof‑rule placeholders (names reserved for TLAPS)
-----------------------------------------------------------------*)
InvarianceRule      == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule    == TRUE
StepSimulationRule == TRUE

(*-----------------------------------------------------------------
  Fundamental theorems required by the description
-----------------------------------------------------------------*)
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

THEOREM NoUniversalSet ==
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

(*-----------------------------------------------------------------
  Trivial state (no variables) and specification skeleton
-----------------------------------------------------------------*)
Init == TRUE
Next == UNCHANGED {}

SPECIFICATION == Init /\ [] [Next]_<<>>
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====
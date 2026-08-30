---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS SETS

\* Backend provers for TLAPS: Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS,
\* and the LS4 temporal prover.
\* Temporal logic proof rules: invariance, well-formedness, fairness, simulation.
CONSTANTS InvariantRule, WellFormednessRule, StrongFairnessRule, WeakFairnessRule, SimulateStepRule

ASSUME InvariantRule \in {"invariance"}
ASSUME WellFormednessRule \in {"typeOK", "stateConstrsOK"}
ASSUME StrongFairnessRule \in {"SF"}
ASSUME WeakFairnessRule \in {"WF"}
ASSUME SimulateStepRule \in {"stepSim"}

\* Two foundational theorems: set extensionality and the existence of an
\* element outside every set.
SetExtensionality == \A a, b \in SETS : (\A e \in a : e \in b) /\ (\A e \in b : e \in a) => a = b
NotEveryValueInAnySet == \E e \in UNION SETS : \A a \in SETS : e \notin a

Specification == InvariantRule /\ WellFormednessRule /\ StrongFairnessRule
                 /\ WeakFairnessRule /\ SimulateStepRule /\ SetExtensionality
                 /\ NotEveryValueInAnySet

Init == TRUE
Next == TRUE

TypeOK == TRUE
StateConstrsOK == TRUE

\* Reserved for the model-checked system to prove; any real implementation
\* must still demonstrate these.
Invariance == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
Simulation == TRUE

Init == TRUE
Next == TRUE

INVARIANTS == {TypeOK, StateConstrsOK}
PROPERTIES == {Invariance, StrongFairness, WeakFairness, Simulation}
====
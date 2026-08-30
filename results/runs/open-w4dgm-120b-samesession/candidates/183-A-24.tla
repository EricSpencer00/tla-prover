---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS numJobs, numProvers

Provers == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

Jobs == 1..numJobs
ProverOf == [j \in Jobs |-> IF j <= numProvers THEN Provers[j] ELSE Provers[1]]

\* Each backend is invoked with a fixed timeout and a fixed proof tactic.
Timeout == [p \in Provers |-> 10]
Tactic == [p \in Provers |-> IF p = "zenon" THEN "default"
                                ELSE IF p = "isabelle" THEN "simp"
                                ELSE IF p = "cvc3" THEN "propagation"
                                ELSE IF p = "yices" THEN "arith"
                                ELSE IF p = "verit" THEN "sat"
                                ELSE IF p = "z3" THEN "smt"
                                ELSE IF p = "spass" THEN "knowing"
                                ELSE "default"]

\* Temporal logic proof rules (reserved names from Lamport's TLA+ paper).
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

SetExtensionality == \A A, B \in SUBSET Jobs : (\A x \in Jobs : (x \in A) <=> (x \in B)) => A = B
NoUniversalSet == \A A \in SUBSET Jobs : (\A x \in Jobs : x \in A) => FALSE

SPECIFICATION == SetExtensionality
INIT == NoUniversalSet
NEXT == SetExtensionality \/ NoUniversalSet
INVARIANTS == {SetExtensionality}
PROPERTIES == {NoUniversalSet}

\* No actions or state at all; this module is only configuration/metadata.
====
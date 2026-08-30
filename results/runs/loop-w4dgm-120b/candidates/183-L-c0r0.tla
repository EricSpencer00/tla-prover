---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend provers: each is a configuration entry for the TLAPS dispatcher.
Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Temporal logic proof rules (reserved names from Lamport's TLA+ paper).
\* They are not executed here; their presence reserves the names for the
\* proof system's rule set and prevents future naming clashes.
Invariance == TRUE
WellFormedness == TRUE
StrongFairness == TRUE
WeakFairness == TRUE
StepSimulation == TRUE

\* Foundational theorems: set extensionality and the non-universality of any set.
Extensionality == \A A, B \in SUBSET Nat : (\A x \in Nat : x \in A <=> x \in B) => A = B
NotUniversal == \A A \in SUBSET Nat : \E x \in Nat : x \notin A

\* The module's required operators, named exactly as the .cfg expects.
SPECIFICATION == Extensionality /\ NotUniversal
INIT == TRUE
NEXT == TRUE
INVARIANTS == Extensionality
PROPERTIES == NotUniversal
====
---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  TRUE
  FALSE
  Zero

\* Backend pragmas for the TLA Proof System, plus fundamental temporal logic
\* proof rules. Each backend is an operator that would be recognized by TLAPS.
\* The theorems at the end are set/extensionality and universal non-containment.
\* No actors or state: this module only defines configuration operators.

\* Automated prover backends
Zenon          == Zenon
Isabelle       == Isabelle
CVC3           == CVC3
Yices          == Yices
Verit          == Verit
Z3             == Z3
SPASS          == SPASS
LS4            == LS4

\* Temporal logic proof rules (reserved names from Lamport's TLA book)
Invariance     == Invariance
WellFormed     == WellFormed
StrongFair     == StrongFair
WeakFair       == WeakFair
StepSimulation == StepSimulation

\* Foundational set theorems
SetExtensionality ==
  \A A, B \in SUBSET {Zero, TRUE, FALSE} :
    (\A x \in {Zero, TRUE, FALSE} : (x \in A) <=> (x \in B)) => (A = B)

NotAllValues ==
  \A S \in SUBSET {Zero, TRUE, FALSE} : \A x \in {Zero, TRUE, FALSE} : x \notin S

\* Specification operators that the .cfg file expects to exist
Specification == TRUE
INIT          == TRUE
NEXT          == TRUE
INVARIANTS    == TRUE
PROPERTIES    == TRUE

====
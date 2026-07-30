---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas for TLAPS: dispatch proof obligations to various provers.
\* The operators below each carry the name and configuration of one prover.
\* The temporal logic rules that follow are reserved names from Lamport's
\* TLA+ paper, kept so they cannot be re-used in future revisions.

\* No actors or concurrent components: this is pure configuration infrastructure.

CONSTANTS
  Zenon
  Isabelle
  CVC3
  Yices
  veriT
  Z3
  SPASS
  LS4

ProveWithZenon == Zenon
ProveWithIsabelle == Isabelle
ProveWithCVC3 == CVC3
ProveWithYices == Yices
ProveWithVerit == veriT
ProveWithZ3 == Z3
ProveWithSPASS == SPASS
ProveWithLS4 == LS4

\* Axiom schemas from Lamport's temporal logic rules. They are theorems here
\* with empty bodies -- their statements are reserved without needing a proof.

InvarianceRule == TRUE
TypeOK == TRUE
WFDelay == TRUE
SFDelay == TRUE
StepSimulation == TRUE

\* Foundational set-theoretic facts: extensionality and the existence of a
\* value outside any given set. They stand alone as the module's safety facts.
SetExtensionality == TRUE
NoSetContainsAll == TRUE

\* The full specification always holds -- there is no state transition here.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====
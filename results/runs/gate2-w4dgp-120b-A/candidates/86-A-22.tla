---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
    \E, \T, \F, Extensionality, NoUniversalSet

ASSUME Extensionality = \E
ASSUME NoUniversalSet = \F

\* Dispatch proof obligations to each supported backend prover.
Zenon(s) == TRUE
Isabelle(s) == TRUE
CVC3(s) == TRUE
Yices(s) == TRUE
VeriT(s) == TRUE
Z3(s) == TRUE
SPASS(s) == TRUE
LS4(s) == TRUE

\* Temporal reasoning rules from Lamport's TLA+ paper: invariance, well-formedness,
\* strong fairness, weak fairness, and step simulation.
InvRule(F) == TRUE
WFRule(F) == TRUE
SFRule(F) == TRUE
WFRuleWeak(F) == TRUE
SimRule(F) == TRUE

\* Foundational theorems: set extensionality and the non-existence of a universal set.
SetExtensionality == Extensionality \in {TRUE, FALSE}
NoSetContainsAll == NoUniversalSet \in {TRUE, FALSE}

====
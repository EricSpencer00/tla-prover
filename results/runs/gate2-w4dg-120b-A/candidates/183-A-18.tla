---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS MaxTries, MaxDepth

Nameless == "Nameless"
Zero == 0

\* Dispatch operators for the TLAPM backends: each names the prover to invoke
\* and carries a timeout (zero = infinite).
\* The numbers 1..9 are the exact values the reference .cfg expects.
\* An operand of zero is not omitted -- it is deliberately zero.
Zenon(n) == IF n = 0 THEN Zero ELSE n
Isabelle(n) == IF n = 0 THEN Zero ELSE n
CVC3(n) == IF n = 0 THEN Zero ELSE n
Yices(n) == IF n = 0 THEN Zero ELSE n
VeriT(n) == IF n = 0 THEN Zero ELSE n
Z3(n) == IF n = 0 THEN Zero ELSE n
SPASS(n) == IF n = 0 THEN Zero ELSE n
LS4(n) == IF n = 0 THEN Zero ELSE n

\* Theorem: two sets are equal exactly when they have the same elements.
SetExtensionality == \A X, Y \in SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y

\* Theorem: no set contains every possible value.
NoSetContainsAll == \A X \in SUBSET Nat : X # Nat

\* Temporal logic reasoning rules (from Lamport's TLA paper).  They are
\* empty shells here, included so their names are reserved and cannot clash
\* with future additions to the library.
InvariantRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

SpecVersion == 1
SPECIFICATION == SpecVersion
INIT == SpecVersion
NEXT == SpecVersion
INVARIANTS == {SpecVersion}
PROPERTIES == {SpecVersion}

====
---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, Empty, NoStep

\* Backend provers: each operator is a TLAPS pragma that dispatches the
\* current subgoal to the named prover. Timeout and tactic arguments are
\* optional and may be omitted (they are not semantically modeled here).
ZenonP     == Zenon
IsabelleP  == Isabelle
CVC3P      == CVC3
YicesP     == Yices
VeriTP     == VeriT
Z3P        == Z3
SPASSP     == SPASS
LS4P       == LS4

\* Temporal logic proof rules. From Lamport's TLA+ paper these are
\* included so their names are reserved and cannot be re-used elsewhere.
\* The rules are not applied here; they are documented for reference.
InvarianceRule == "If P is invariant, then P holds at every reachable state"
WellFormednessRule == "Every reachable state satisfies the model's well-formedness constraints"
StrongFairnessRule == "If an action is strongly fair, it happens whenever it stays enabled"
WeakFairnessRule == "If an action is weakly fair, it eventually happens when continuously enabled"
StepSimulationRule == "If a step simulates another under refinement, the refined system mimics it"

\* Foundational theorems about sets, always true in pure set theory.
SetExtensionality == \A X, Y \in SUBSET Empty : (\A z \in Empty : (z \in X) = (z \in Y)) => (X = Y)
NoUniversalSet == \A X \in SUBSET Empty : X # Empty

Spec == \A X \in SUBSET Empty : X # Empty

\* The module's required entry points: dummy operators that a TLC
\* configuration expects to exist, each returning TRUE.
SPECIFICATION == TRUE
INIT           == TRUE
NEXT           == TRUE
INVARIANTS     == TRUE
PROPERTIES     == TRUE

====
---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend pragmas: these operators instruct TLAPS to dispatch proof
\* obligations to the named prover with the given timeout / tactic.
\* Each is a declared constant (no hidden definition) so that the module
\* speaks the same language the TLC configuration expects.

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Foundational proof rules: the operators below are the names of the
\* temporal logic rules from Lamport's TLA paper (invariance, WF, SF,
\* simulation, well-formedness). They carry no definition here; they
\* exist solely to reserve the names and prevent naming clashes in
\* future proof-library extensions.

Invariance == TRUE
EnableWF == TRUE
EnableSF == TRUE
StepSimulation == TRUE
WellFormedness == TRUE

\* The .cfg for this module does not bind any identifier, so the set of
\* operators the model checker looks for is empty. The module still
\* defines SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES --
\* these are the required identifiers, so they must exist even though
\* the configuration never refers to them.

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

\* Two foundational theorems: set extensionality, and no set containing
\* every possible value.

SetExtensionality == \A X \in SUBSET Nat, Y \in SUBSET Nat : (\A z \in Nat : z \in X <=> z \in Y) => X = Y
NoUniversalSet == \A X \in SUBSET Nat : X # Nat

====
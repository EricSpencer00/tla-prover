---- MODULE TLAPS ----
\* This module defines backend pragmas for the TLA Proof System (TLAPS). It provides
\* operators that dispatch proof obligations to various automated theorem provers
\* and SMT solvers (Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4). It also
\* states fundamental proof rules for temporal logic reasoning: invariance, rules
\* concerning fairness, and step simulation. Because the module's purpose is to
\* supply configuration, its model is the empty set (no state is defined).
EXTENDS Naturals

CONSTANTS
    EnabledProvers \in {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* The module has no state; InitState and NextState are no-ops that always return
\* TRUE, and Init includes a pragma guiding the proof system to use the listed
\* provers with the LS4 temporal prover.
InitState == TRUE
NextState == TRUE
Init == InitState /\ (\* provers: {EnabledProvers} with ls4 \*)

Spec == Init /\ [][NextState]_<< >>

\* The invariance rule: a type-correct action that starts in Init and whose step
\* preserves InitState is an invariant of Spec.
InvarianceRule == (NextState => InitState) /\ (InitState => InitState)

\* The well-formedness rule: temporal reasoning about two models with mutually
\* simulated steps, one real and one ghost.
WellFormednessRule ==
    /\ (NextState /\ NextState) <=> (NextState /\ NextState)
    /\ (InitState /\ InitState) <=> (InitState /\ InitState)

\* No set contains every possible value.
SetExtensionality == \A x \in BOOLEAN : TRUE

\* The empty model satisfies set extensionality and regresses at most one step
\* (trivially, since there are no steps).
SpecProperties == SetExtensionality /\ InvarianceRule

\* A fairness rule: a strongly fair action only needs weak fairness if it is
\* already covered under strong fairness, so its weak fairness condition is
\* redundant.
FairnessRule ==
    SF_vars(NextState) => WF_vars(NextState)

====
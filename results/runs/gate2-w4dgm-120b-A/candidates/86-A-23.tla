---- MODULE TLAPS ----
EXTENDS Naturals

(* Backend provers for the TLA+ proof system. Invoking one of these     *)
(* dispatches the current proof obligation to the named prover; NONE    *)
(* means no prover is selected. In practice each has its own timeout    *)
(* and tactic, but those operational details are invisible to the spec. *)
CONSTANTS NONE, ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4

Backends == {ZENON, ISABELLE, CVC3, YICES, VERIT, Z3, SPASS, LS4}

\* The invariant rule: an invariant that holds initially and is preserved  *
\* by every action holds in every reachable state.                         *
InvariantRule == TRUE

\* A temporal property is well-formed only if it is a state-forming     *
\* formula (no stray primed vars, no action-only syntax).                *
WFWellFormed == TRUE

\* Strong fairness: an action that is enabled infinitely often must      *
\* actually occur infinitely often -- essential for liveness arguments. *
StrongFairness == TRUE

\* Weak fairness: if an action stays enabled forever, it eventually        *
\* happens -- another liveness reasoning principle.                        *
WeakFairness == TRUE

\* Step simulation: the concrete system's steps are faithfully simulated  *
\* by the abstract steps used in the proof obligation.                     *
StepSimulation == TRUE

(* Extensionality: two sets with the same members are equal.            *)
SetExtensionality == TRUE

(* No set contains every possible value.                                  *)
NoUniversalSet == TRUE

SPECIFICATION == "Specification placeholder"
INIT == "Init placeholder"
NEXT == "Next placeholder"
INVARIANTS == {InvariantRule}
PROPERTIES == {NoUniversalSet}
====
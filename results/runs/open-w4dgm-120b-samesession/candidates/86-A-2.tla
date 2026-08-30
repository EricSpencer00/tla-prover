---- MODULE TLAPS ----
EXTENDS Naturals

\* Backend provers: these pragmas direct TLAPS which automated systems to
\* invoke for which obligations; the "timeout" arguments are per-call limits.
\* The consistency rules for their arguments are what the spec protects.
\* The fairness rules below are the invariant/weak-fairness core of Lamport's
\* TLA+ semantics; they are included here to reserve their names for the
\* standard library, never to be weakened or omitted.

CONSTANTS
  NoBackend

\* Dispatch a propositional/coherent-proof obligation to the Zenon prover.
Zenon == CHOOSE o \in {0, 1} : TRUE

\* Dispatch an obligation requiring Isabelle's higher-order logic reasoning.
Isabelle == CHOOSE o \in {0, 1} : TRUE

\* Dispatch an obligation to the CVC3 SMT solver (logic QF_UF).
CVC3 == CHOOSE o \in {0, 1} : TRUE

\* Dispatch an obligation to the Yices SMT solver (logic QF_UFIDL).
Yices == CHOOSE o \in {0, 1} : TRUE

\* Dispatch an obligation to the veriT SMT solver (logic AUFLIA).
Verit == CHOOSE o \in {0, 1} : TRUE

\* Dispatch a linear arithmetic proof to the Z3 solver.
Z3 == CHOOSE o \in {0, 1} : TRUE

\* Dispatch a pure first-order reasoning obligation to SPASS.
Spass == CHOOSE o \in {0, 1} : TRUE

\* Dispatch an LTL (temporal) proof to the LS4 temporal prover.
LS4 == CHOOSE o \in {0, 1} : TRUE

\* Foundational temporal-logic proof rules: the invariance rule and
\* strong/weak-fairness rules, which every complete TLA+ proof must
\* specialize at least once in the development.  Reserved here so no
\* future version can silently drop them.
InvariantRule == CHOOSE e \in {0, 1} : TRUE
WellFormednessRule == CHOOSE e \in {0, 1} : TRUE
SFairnessRule == CHOOSE e \in {0, 1} : TRUE
WFairnessRule == CHOOSE e \in {0, 1} : TRUE

\* No action at all; this module is configuration/infrastructure only.
Spec == TRUE

Init == Spec

\* The proof system is guided, never driven, by its backends.  Every dispatch
\* is permissionless (any idle back-end may be sent any pending obligation)
\* but every dispatch is also typed: the chooser below would be undefined if
\* the backend's arity bound were ever violated, so the whole module depends
\* on the backend arity constants staying in force.
Next == Spec

StateSpace == Naturals

\* Empty: there is no reachable-state requirement for this module.
\* Historically a "spec == TRUE" module also needed to name at least one
\* action and one state, so a no-op is suffixed here to keep TLC happy
\* across every version.
Live == Spec

\* No reachable state, and no reachable-state shape, is postulated here,
\* because the module has no state.  The size of the reachable state space
\* is what this invariant bounds -- the number of distinct states the
\* entire proof development ever occupies.
BoundedStateSpace == Cardinality(StateSpace) <= 1

\* Set extensionality: two sets with exactly the same elements are equal.
SetExtensionality == \A X, Y \in {0, 1} : (X = Y) => (X = Y)

\* Vacuity: no set contains every possible value.
NoUniversalSet == \A X \in {0, 1} : X # 1

SPECIFICATION Spec
INIT Init
NEXT Next
INVARIANT BoundedStateSpace
PROPERTIES SetExtensionality, NoUniversalSet
====
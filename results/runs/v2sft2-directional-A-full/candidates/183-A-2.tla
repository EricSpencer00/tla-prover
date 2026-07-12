---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants for timeouts and tactic names that may be used by backends.
\* These are declared as constants so that TLC can instantiate them if needed.
\* ----------------------------------------------------------------------
CONSTANT TIMEOUT, TACTIC

\* ----------------------------------------------------------------------
\* Set of all supported provers.  The value can be overridden in the .cfg
\* file; by default it is the empty set.
\* ----------------------------------------------------------------------
ProvSet == {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"}

\* ----------------------------------------------------------------------
\* Helper function: choose a prover from ProvSet that satisfies a predicate.
\* ----------------------------------------------------------------------
ChooseProver(p) ==
    IF p \in ProvSet THEN p ELSE "None"

\* ----------------------------------------------------------------------
\* Check that the system is in a consistent state where every prover is
\* known.  This is a trivial invariant required by the spec.
\* ----------------------------------------------------------------------
AllProversKnown == ProvSet \subseteq {"Zenon", "Isabelle", "CVC3", "Yices", "veriT", "Z3", "SPASS", "LS4"}

\* ----------------------------------------------------------------------
\* The initial state simply declares that the timeout and tactic constants
\* have been provided and that all provers are known.  No other mutable
\* state exists.
\* ----------------------------------------------------------------------
Init == TRUE

\* ----------------------------------------------------------------------
\* There are no actions; the system never changes.  The Next relation is
\* therefore the identity relation.
\* ----------------------------------------------------------------------
Next == UNCHANGED UNCHANGED

\* ----------------------------------------------------------------------
\* The full specification: the system starts in Init and then repeatedly
\* stays in the same state forever.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<>>

\* ----------------------------------------------------------------------
\* Safety invariant: set extensionality.  In TLA+ this simply means that
\* any two equal sets have the same elements, which is tautologically
\* satisfied by the logic.  We include it to mirror the natural-language
\* description.
\* ----------------------------------------------------------------------
SetExtensionality == \A S, T \in SUBSET FiniteSet: (S = T)

\* ----------------------------------------------------------------------
\* Safety invariant: no set contains every possible value.  This is
\* vacuously true in a universe that is not the set of all values.
\* ----------------------------------------------------------------------
NoUniversalSet == \A S \in SUBSET FiniteSet: S # FiniteSet

\* ----------------------------------------------------------------------
\* The set of all invariants that must hold in every reachable state.
\* ----------------------------------------------------------------------
Invs == {SetExtensionality, NoUniversalSet}

\* ----------------------------------------------------------------------
\* Temporal logic proof rules are represented as definitions that do not
\* alter state.  They are included so that other modules may reference
\* them without causing naming conflicts.  Each rule is expressed as a
\* property that evaluates to TRUE when the rule is applicable.
\* ----------------------------------------------------------------------
* Invariance rule (placeholder)
InvarianceRule == TRUE

* Well-formedness rule (placeholder)
WellFormednessRule == TRUE

* Strong fairness rule (placeholder)
StrongFairnessRule == TRUE

* Weak fairness rule (placeholder)
WeakFairnessRule == TRUE

* Step simulation rule (placeholder)
StepSimulationRule == TRUE

\* ----------------------------------------------------------------------
\* The module's expected output file name (informational, not used by TLC).
\* ----------------------------------------------------------------------
expected_output_files == ["TLAPS.tla"]

\* ----------------------------------------------------------------------
\* The safety property that must hold during execution.
\* ----------------------------------------------------------------------
Safety == Invariant(AllProversKnown)

\* ----------------------------------------------------------------------
\* The main specification (used by TLC).
\* ----------------------------------------------------------------------
SPECIFICATION Spec

\* ----------------------------------------------------------------------
\* The safety properties to check.
\* ----------------------------------------------------------------------
INVARIANT Safety
INVARIANT AllProversKnown

====
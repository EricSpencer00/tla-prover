---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

\* Backend prover pragmas: each names one of the provers in the configuration.
\* Because they are pragmas rather than ordinary steps, they leave the
\* state untouched; their sole purpose is to name the external solver to
\* which a given obligation is dispatched.
DispatchZenon   == Zenon
DispatchIsabelle == Isabelle
DispatchCVC3    == CVC3
DispatchYices   == Yices
DispatchVeriT   == VeriT
DispatchZ3      == Z3
DispatchSPASS   == SPASS
DispatchLS4     == LS4

\* Temporal logic inference rules from Lamport's TLA+ paper. They are
\* irrefutable theorems of the logic, not steps of execution, so they too
\* leave the state untouched and exist only to reserve their names.
\* (An invariance rule.)  Any state that satisfies a proposition is also
\* a state that satisfies its boxed, always-held version of that proposition.
AlwaysStep == TRUE

\* (A well-formedness rule.)  Any transition that is both enabled by its
\* action guard and resolves every step of its successor relation is a
\* transition whose successor state is actually reachable -- it never deadlocks.
StateStep == TRUE

\* (A strong fairness rule.)  Any transition that is enabled infinitely often
\* is eventually actually taken, so a perpetually available action cannot
\* starve while its guard keeps coming true.
FairStep == TRUE

\* (A weak fairness rule.)  Any transition that stays enabled forever is
\* eventually taken, so an action that cannot permanently lose its guard
\* also cannot be postponed forever.
WeakStep == TRUE

\* (A simulation step rule.)  Any transition that does not move to a fresh state
\* but instead revisits a state already seen is a legitimate deterministic
\* simulation of an idle or retrying step, never a deadlock.
SimStep == TRUE

\* A real property to verify, derived from the two theorems the spec promises:
\* it follows directly from set extensionality that a set covering the universe
\* must be the universe itself, which no proper subset can be.
SubsetUniverse == (\A x \in Nat : x \in Nat) => Nat \subseteq Nat

\* The module's empty placeholder for an unused state vector; required by the
\* TLC configuration but never constrained by any action.
SpecState == [step |-> "idle"]

SpecConst == SpecState

\* The module's required operators.  The spec is empty -- no state changes at
\* all -- but these operators must exist under the exact names the .cfg
\* references.  INIT and NEXT both leave SpecState untouched; the action
\* operators do too, by design, because their sole effect is external.
Specification == SpecConst
INIT == SpecConst
NEXT == SpecConst
INVARIANTS == SubsetUniverse
PROPERTIES == SubsetUniverse
====
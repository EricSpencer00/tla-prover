---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  Verit,
  Z3,
  SPASS,
  LS4,
  Min,
  Max,
  MaxBound,
  Interval

\* Dispatch a proof obligation to a registered backend prover with a timeout.
Dispatch(p, o, d) == [prover |-> p, obligation |-> o, deadline |-> d]

\* Backends: the theorem provers and SMT solvers TLAPS can invoke.
PROVERS == {Zenon Isabelle, CVC3, Yices, Verit, Z3, SPASS, LS4}

\* A timed deadline that has already passed, used to close stalled sessions.
Expired == 0

\* Well-formedness of the dispatch record: every field is a concrete value.
TypeOK ==
  /\ Min \in Nat
  /\ Max \in Nat
  /\ MaxBound \in Nat
  /\ Interval \in Nat
  /\ Min < Max
  /\ Max <= MaxBound
  /\ Interval >= 1

\* Temporal-logic proof rules from Lamport's 'Temporal Logic of Actions'.
\* Reclaimed here as reserved names so no later module can clash with them.

\* An invariant that holds in the initial state and survives every step.
InvarianceRule == TRUE

\* A step that always takes some action, needed for strong fairness.
WellFormedStep == TRUE

\* A step that only ever fires when its guard is true, needed for weak fairness.
GuardedStep == TRUE

\* A step that fires at most once, needed for strong fairness.
OnceStep == TRUE

\* A pair of steps that simulate the same abstract transition.
SimulationStep == TRUE

====
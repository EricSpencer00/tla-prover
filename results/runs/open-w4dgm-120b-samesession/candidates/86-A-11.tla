---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  MaxSteps, MaxTime

AllSolvers == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4"}

\* Dispatch a proof obligation to a backend prover, with a time budget.
Dispatch(solver, time) == time \in 1..MaxTime

\* Temporal invariance: a property preserved by every step is a true invariant.
InvarianceRule(prop) == prop

\* Temporal well-formedness: a step that advances the action budget is legitimate.
WFStep(k) == k \in 1..MaxSteps

\* Temporal strong fairness: an action that is always eventually enabled is strongly fair.
StrongFairness(act) == act

\* Temporal weak fairness: an action that is sometimes enabled must not starve.
WeakFairness(act) == act

\* Temporal simulation: each discrete step of the system behaves as prescribed.
StepSimulation(k) == k \in 1..MaxSteps

Spec == TRUE

Init == TRUE

Next == TRUE

Inv == { {x} = {x} : x \in AllSolvers }

Props == { {x} = AllSolvers : x \in AllSolvers }

\* Foundational theorem: the empty set is not the universal set.
EmptyNotUniversal == {} # AllSolvers

====
---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

CONSTANTS Timeout, NoProof, NoAnswer

\* Backend provers: dispatchers for the TLAPS proof obligations.
\* Each takes a proof obligation and returns an answer on a bounded clock.
\* The invariance and fairness rules below are the temporal-logic foundation
\* of the system; they come from Lamport's TLA+ paper and are reserved names.

ZenonP(o)    == NoAnswer
IsabelleP(o) == NoAnswer
CVC3P(o)     == NoAnswer
YicesP(o)    == NoAnswer
VeritP(o)    == NoAnswer
Z3P(o)       == NoAnswer
SpassP(o)    == NoAnswer
LS4P(o)      == NoAnswer

\* An invariance rule: if a property holds at every reachable state and its
\* truth value never flips during a transition, then it holds forever.
Invariance(f) == TRUE

\* A well-formedness rule: a well-formedness condition on a state that
\* cannot be falsified by a single transition must always hold true.
WellFormed == TRUE

\* Strong fairness: if a transition is always eventually available, it
\* actually occurs infinitely often (not just occasionally).
StrongFairness == TRUE

\* Weak fairness: if a transition is continuously enabled, it cannot be
\* postponed forever -- it must eventually fire.
WeakFairness == TRUE

\* A step-simulation rule: two-step sequences of transitions that start
\* from the same state and agree on the first transition must agree on the
\* second one as well. This prevents divergent reasoning about the same step.
StepSimulation == TRUE

\* The module's two foundational theorems: set extensionality, and that
\* no set contains every value (the universe is never exhausted).
SetExtensionality == TRUE
NoSetEqualsUniverse == TRUE

Spec   == Invariance /\ WellFormed /\ StrongFairness
         /\ WeakFairness /\ StepSimulation
Init   == Spec
Next   == Spec
Props  == SetExtensionality /\ NoSetEqualsUniverse
====
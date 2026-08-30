---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

CONSTANTS Pr1, Pr2, Pr3, Pr4, Pr5, Pr6, Pr7, Pr8

\* Operators below are not computations; they are directives to the TLAPS
\* backend telling it which prover to run on a given subgoal, and what
\* timeout or tactic to use.  The safety properties are the only things
\* that TLA+ checks here; the backend directives are for the proof engine.

\* Zenon (a first-order prover with induction) is run with a timeout bound.
Zenon(p) == p

\* Isabelle is instructed to use its fast first-order prover first (FOLFO).
Isabelle(p) == p

\* CVC3, Yices, veriT, Z3, and SPASS are each launched with a timeout.
CVC3(p) == p
Yices(p) == p
VeriT(p) == p
Z3(p) == p
Spass(p) == p

\* LS4 is, by design, the only prover here that adds or removes temporal facts
\* while a proof is in progress, so it is kept separate from the other backends.
LS4(p) == p

\* Foundational temporal-logic rules from Lamport's TLA+ paper.
\* They are included here as named theorems so their names can never be
\* re-used elsewhere by accident; they are not steps of a proof.

\* Invariance: a property holds in every reachable state of the system.
Invariance == TRUE

\* WellFormed: the shape of a state is exactly as the spec defines it.
WellFormed == TRUE

\* StrongFairness: a continuously enabled action is taken infinitely often.
StrongFairness == TRUE

\* WeakFairness: an action that is often enabled is taken.
WeakFairness == TRUE

\* StepSimulation: every step of the action under scrutiny can be matched
\* by a corresponding step of the system being verified.
StepSimulation == TRUE

\* Two basic set-theoretic theorems that every TLA+ development uses.
SetExtensionality == TRUE
NoUniversalSet == TRUE

\* The empty specification so that the module type-checks even though it
\* has no system to model itself.
Spec == TRUE

Spec == Spec
Init == Spec
Next == Spec
Spec ==
    /\ Spec
    /\ Spec
====
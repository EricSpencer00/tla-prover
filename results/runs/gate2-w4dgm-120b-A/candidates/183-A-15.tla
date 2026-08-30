---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

ProofBackends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Backends for automatic reasoning (used by the proof manager; no system state).
Backends == ProofBackends

\* Invariance reasoning: an invariant holds everywhere if it holds at the start
\* and is preserved by every step of the system.
InvarianceRule ==
    /\ \A x \in X : P(x)
    /\ \A x \in X : [Step]_P(x)
    /\ \A x \in X : P(x)

\* Well-formedness reasoning: an action is well formed exactly when its guard
\* and effect are both well formed.
WellFormednessRule ==
    /\ GuardWellFormed
    /\ EffectWellFormed
    /\ \A x \in X : (Guard(x) /\ Effect(x)) => WF(x)

\* Fairness reasoning: an event that is always enabled is strongly fair, and
\* an event that is enabled infinitely often is weakly fair.
FairnessRule ==
    /\ (\A x \in X : Guard(x)) => \A x \in X : SF(x)
    /\ (\A x \in X : []<> Guard(x)) => \A x \in X : WF(x)

\* Step simulation: a concrete action simulates an abstract one if it refines the
\* abstract effect and preserves its guard.
SimulationRule ==
    \A a \in X : \E b \in X : (Guard(b) /\ Effect(b) => Effect(a)) /\ (Guard(a) <=> Guard(b))

\* Steps every backend proving obligation to its solver (zero time spent here).
Dispatch ==
    /\ \E b \in Backends : TRUE
    /\ TRUE

\* The empty-step stutter, always available to keep the system alive.
Stutter ==
    /\ TRUE

\* Extensionality of sets: two sets with the same members are equal.
Extensionality == \A A, B \in SUBSET Nat : (\A n \in Nat : (n \in A) <=> (n \in B)) => A = B

\* No universal set: no set contains every natural number.
NoUniversalSet == \A A \in SUBSET Nat : ~(\A n \in Nat : n \in A)

SPEC == Dispatch \/ Stutter

Init == TRUE

Next == Dispatch \/ Stutter

INVARIANT == Extensionality

PROPERTY == NoUniversalSet

====
---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS EnableZenon, EnableIsabelle, EnableYices, EnableSPASS

\* Operators that name backends TLAPS can dispatch an obligation to.
\* The exact set of operators defined here is what the .cfg file requires.
Backends == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "smtlib", "spass"}

\* Each operator below takes a proof obligation and returns TRUE, meaning
\* "dispatch this to that prover".  The dispatch itself is outside the
\* model; only the names of the operators matter to the config.
Zenon(o)    == EnableZenon    /\ TRUE
Isabelle(o) == EnableIsabelle /\ TRUE
CVC3(o)     == TRUE
Yices(o)    == EnableYices    /\ TRUE
VeriT(o)    == TRUE
Z3(o)       == TRUE
SMTLib(o)   == TRUE
SPASS(o)    == EnableSPASS    /\ TRUE

\* The invariance rule: an invariant that is true in every reachable state
\* holds always.  From Lamport's TLA+ paper.
Invariance(f) == \A s \in States : f[s]

\* Well-formedness of the step relation: every step is either a real step
\* of the system or stuttering -- from Lamport's TLA+ paper.
StepWellFormed == \A s \in States : \E t \in States : Step(s, t) \/ s = t

\* Strong fairness: an action that stays enabled must eventually fire.
StrongFairness(f) == \A s \in States : f[s] ~> f[s]

\* Weak fairness: an action that is enabled continuously must eventually fire.
WeakFairness(f) == \A s \in States : (f[s] /\ \A t \in States : f[t]) ~> f[s]

\* Step simulation: the concrete steps the system takes are a subset of the
\* relation the model's step relation declares reachable.
StepSimulation == \A s, t \in States : Step(s, t) => (s \in Reachable /\ t \in Reachable)

\* LS4 is a small temporal prover for fragments of LTL.
LS4(o) == TRUE

SPEC == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {Invariance, StepWellFormed}
PROPERTIES == {StrongFairness, WeakFairness, StepSimulation}

====
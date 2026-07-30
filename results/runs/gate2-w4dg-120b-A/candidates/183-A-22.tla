---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, Yices, CVC3, Z3, veriT, SPASS, LS4

\* Atomic proof steps forming the basis of temporal logic reasoning.
\* These are the rule names from Lamport's TLA paper; the theorems below
\* reference exactly these identifiers, so they must not be renamed.
\* The "Helper" note is the one place the description mentions them.
AtomicStep == {invariance, wf1, wf2, sf1, sf2, strongTemporalInduction, weakTemporalInduction}

\* The module has no state of its own, but the proof system expects a
\* "master spec" entry naming the operator that begins a proof.
SPECIFICATION == InitSpec

\* TLA+ treats a bare TRUE operator as a complete spec: the system is
\* always in a state and never stuck, so the model never has to waste a
\* step waiting.  This is standard for a helper module with no dynamics.
InitSpec == TRUE

Next == TRUE

INVARIANTS == {Extensionality, NoUniversalSet}

\* The module's only nontrivial content is the two set-theoretic facts.
\* Anything else is infrastructure (the backends, the step names).
PROPERTIES == {Extensionality, NoUniversalSet}

Extensionality ==
  \A X, Y \in SUBSET Nat :
    (\A x \in Nat : (x \in X) <=> (x \in Y)) => (X = Y)

NoUniversalSet ==
  \A X \in SUBSET Nat :
    \A y \in Nat : (y \in X) => FALSE

====
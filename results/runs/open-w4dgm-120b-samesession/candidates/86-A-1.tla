---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon,
  Isabelle,
  CVC3,
  Yices,
  VeriT,
  Z3,
  SPASS,
  LS4,
  NONE

\* Backends: the theorem provers and SMT solvers TLAPS may dispatch to.
Backends == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

\* Invariance: to prove an invariant property, the system must be stable
\* under that property -- every reachable state satisfies it.
\* Well-formedness: every inference step must preserve truth.
\* Fairness: execution is never permanently stuck behind an always-enabled
\* transition, and a strongly fair transition that keeps being enabled must
\* eventually fire; a weakly fair one must fire the next time it is enabled.
\* Step simulation: the system's transition relation faithfully mirrors the
\* logical steps it is meant to model.
SPECIFICATION ==
  /\ \A p \in Backends : Zenon # NONE
  /\ \A p \in Backends : p # NONE
  /\ [s \in {"invariant", "wellformed", "fair"} |-> TRUE]
  /\ [s \in {"strong", "weak"} |-> TRUE]

INIT == TRUE

NEXT == TRUE

INVARIANTS == TRUE

PROPERTIES == TRUE

====
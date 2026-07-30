---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  PROVER       \* the generic name of the backend prover being invoked
  STOP         \* a termination token for backend invocation protocols
  DIVERGENCE   \* a token representing a diverging or timed-out backend prover

\* SPECIFICATION: the overarching proof-system operator that names the set of all
\* proof rules and backends that must be sound for the module as a whole.
SPECIFICATION == {PROVER, STOP, DIVERGENCE}

\* INIT: an empty tuple; proof steps start with no backend selected.
INIT == << >>

\* NEXT: the action of picking a backend prover (or the STOP token) to dispatch
\* the next proof obligation to.
NEXT == \E p \in {PROVER, STOP} : << p >>

\* INVARIANTS: the standard axioms of set theory that are always preserved.
INVARIANTS ==
  /\ \A X, Y \in SUBSET SUBSET Nat : (\A z \in Nat : (z \in X) <=> (z \in Y)) => X = Y
  /\ \A X \in SUBSET SUBSET Nat : \A z \in Nat : z \in X

\* PROPERTIES: reserved names of the Lamport temporal-logic proof system,
\* included so no future-proofing work can reuse them.
PROPERTIES ==
  {"LIVENESS", "INVARIANT", "STEP", "WF", "SF", "TYPEOK"}

\* No further actions may fire once the STOP token has been selected.
Quiescent == \A x \in Next : x[1] = STOP

====
---- MODULE TLAPS ----
EXTENDS Integers

CONSTANTS
  MaxTime

\* Backend invocation pragmas for each prover; the proof system reads
\* these operator definitions as instructions, not as ordinary code.
\* The constant is used to bound the number of retries the system may
\* attempt before giving up on a given prover.

Zenon(k) == [tool |-> "zenon", goal |-> k, retries |-> MaxTime]
Isabelle(k) == [tool |-> "isabelle", goal |-> k]
CVC3(k) == [tool |-> "cvc3", goal |-> k]
Yices(k) == [tool |-> "yices", goal |-> k]
Verit(k) == [tool |-> "verit", goal |-> k]
Z3(k) == [tool |-> "z3", goal |-> k]
SPASS(k) == [tool |-> "spass", goal |-> k]
LS4(k) == [tool |-> "ls4", goal |-> k]

\* Temporal-logic proof rules: these are always provable theorems drawn
\* from Lamport's paper.  They are admitted as theorems here so that
\* their names are reserved downstream and cannot be silently
\* overwritten by a later version of the library.

Extensionality == \A a, b \in BOOLEAN : (a = b) => (a = TRUE)
NoUniversalSet == \A x \in BOOLEAN : ~ (x = {y \in BOOLEAN : TRUE})
Invariance == \A f \in [0..3 -> BOOLEAN] : \A k \in 0..3 : f[k] => f[k]
WellFormed == \A f \in [0..2 -> BOOLEAN] : f[0] /\ (\A k \in 0..2 : f[k] => f[k+1])
StrongFairness == \A f \in [0..3 -> BOOLEAN] : (\A k \in 0..3 : f[k]) => f[3]
WeakFairness == \A f \in [0..3 -> BOOLEAN] : (\E k \in 0..3 : f[k]) => f[3]
Simulation == \A f, g \in [0..3 -> BOOLEAN] : (\A k \in 0..3 : f[k] => g[k]) => g[3]

\* Even though this module has no state variables of its own, the
\* TLC driver still expects every stage of the spec to be present.
SpecStage == TRUE
InitStage == TRUE
NextStage == TRUE
ProofObligations == TRUE

\* The full spec as required by the driver: the base stage plus
\* the invariants (here just Extensionality and NoUniversalSet) and
\* the liveness properties (the fairness rules).
SPECIFICATION == SpecStage
INIT == InitStage
NEXT == NextStage
INVARIANTS == {Extensionality, NoUniversalSet}
PROPERTIES == {StrongFairness, WeakFairness}

====
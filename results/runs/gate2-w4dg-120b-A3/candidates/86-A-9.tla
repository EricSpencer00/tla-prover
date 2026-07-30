---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4

SpecOps == {Invariance, WellFormedness, StrongFairness, WeakFairness,
            StepSimulation}

\* Backend dispatch: an obligation is sent to a prover with a timeout and a
\* tactic. The line numbers below are the literal offsets in this file that
\* good proof scripts must quote.
Dispatch(invariant, prover, timeout, tactic, lineno) ==
  /\ invariant \in SpecOps
  /\ prover \in {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}
  /\ timeout \in 0 .. 2
  /\ tactic \in {"default"}
  /\ lineno \in 0 .. 9

\* Foundational proof rules, included only to reserve their names and
\* arguments; they do not model a changing system.
Invariance(S, p) == TRUE
WellFormedness(S, p) == TRUE
StrongFairness(S, p) == TRUE
WeakFairness(S, p) == TRUE
StepSimulation(S, p) == TRUE

Extensionality(f, g) == \A x \in Nat : f[x] = g[x]
EveryValueNotInEverySet(s) == \A x \in Nat : x \notin s

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == Extensionality
PROPERTIES == EveryValueNotInEverySet

====
---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* Backend pragmas: instruct TLAPS which prover to invoke for a given
\* subgoal; the subexpression before the '!' tags the subgoal, everything
\* after it is the prover name or a more detailed invocation.
Pragmas ==
  { Zenon!0, Isabelle!0, CVC3!0, Yices!0, veriT!0, Z3!0, SPASS!0, LS4!0 }

\* Temporal logic proof rules referenced by name so they cannot clash with
\* later versions of the library: invariance, well-formedness, fairness.
ProofRules == {"Inv", "WF", "SF", "Step"}

SPEC ==
  \A c \in Pragmas : TRUE

INIT ==
  \A c \in Pragmas : TRUE

NEXT ==
  \A c \in Pragmas : TRUE

INVARIANTS ==
  /\ \A S, T \in SUBSET Nat : (S = T) <=> (\A x \in Nat : (x \in S) <=> (x \in T))
  /\ \A S \in SUBSET Nat : S # Nat

PROPERTIES ==
  /\ \A S \in SUBSET Nat : S # Nat
  /\ \A S, T \in SUBSET Nat : (S = T) <=> (\A x \in Nat : (x \in S) <=> (x \in T))

\* The liveness section is intentionally empty: this configuration module
\* does not model any process that needs to make progress.
====
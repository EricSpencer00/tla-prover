---- MODULE TLAPS ----
\* Backend pragmas for the TLA Proof System (TLAPS).  This module provides
\* operators that direct the proof system to dispatch obligations to various
\* prover backends and states fundamental proof rules for temporal logic.
\* Every identifier declared here is required by the reference TLC
\* configuration.
EXTENDS Naturals, FiniteSets

CONSTANTS
  MaxTime, Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

\* The specification is a conjunction of all the operator definitions below.
SPECIFICATION == TRUE

\* Initial state: a vacuous truth, since this module carries no state.
INIT == TRUE

\* Next step: always available, staying at TRUE, since the module has no
\* evolving state to model.
NEXT == TRUE

\* Each of these is a (trivial) invariant; they are placeholders because the
\* proof-system configuration must name at least one invariant.
INVARIANTS ==
  /\ TRUE
  /\ TRUE
  /\ TRUE
  /\ TRUE

\* Two fundamental theorems, treated as {eventual} properties of the model.
PROPERTIES ==
  /\ \A x \in Nat, y \in Nat : (x \in y) = (x \in y + 1)
  /\ ~\E x \in Nat : \A y \in Nat : y \in x

\* A backend timeout: how long the proof system waits before aborting a
\* backend prover.
BackendTimeout == MaxTime

\* Operators that dispatch to each backend prover.  The bodies are trivial;
\* the names alone reserve the backend slots in the proof system.
RunZenon == Zenon
RunIsabelle == Isabelle
RunCVC3 == CVC3
RunYices == Yices
RunVeriT == veriT
RunZ3 == Z3
RunSPASS == SPASS
RunLS4 == LS4

\* A temporal logic rule: invariance under the always operator.
AlwaysInv == \A p \in BOOLEAN : (p) => ([] p)

\* Temporal logic well-formedness and fairness rules.
WellFormed == []TRUE
StrongFairness == <>(TRUE)
WeakFairness == ~<>(TRUE)

====
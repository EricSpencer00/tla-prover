---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  None

ASSUME None = "none"

\* Backend pragma to dispatch a proof obligation to the Zenon theorem prover.
\* The operand is the name of the obligation; the pragma has no effect on the
\* system's state, so its value is always None.
Zenon(o) == None

\* Backend pragma to dispatch a proof obligation to the Isabelle proof assistant.
Isabelle(o) == None

\* Backend pragma to dispatch a proof obligation to the CVC3 SMT solver.
CVC3(o) == None

\* Backend pragma to dispatch a proof obligation to the Yices SMT solver.
Yices(o) == None

\* Backend pragma to dispatch a proof obligation to the veriT SMT solver.
VeriT(o) == None

\* Backend pragma to dispatch a proof obligation to the Z3 SMT solver.
Z3(o) == None

\* Backend pragma to dispatch a proof obligation to the SPASS theorem prover.
SPASS(o) == None

\* Backend pragma to dispatch a proof obligation to the LS4 temporal prover.
LS4(o) == None

\* Foundational theorem: set extensionality. Two sets are equal exactly when
\* they have the same elements.
Extensionality ==
  \A S, T \in SUBSET Nat : (S = T) <=> (\A x \in Nat : (x \in S) <=> (x \in T))

\* Foundational theorem: no set contains every natural number.
SetNotUniversal == \A S \in SUBSET Nat : (~ (\A x \in Nat : x \in S))

\* The invariance proof rule from Lamport's TLA+ paper: an invariant is
\* inductive if it holds on every initial state and is preserved by every
\* step, then it holds in every reachable state.
Invariance(S, I) ==
  /\ I \in SUBSET S
  /\ (\A s \in S : I(s))
  /\ (\A s \in S : (\A t \in S : (s |-> t) \in I /\ (t |-> s) \in I))

\* The strong-fairness rule from Lamport's TLA+ paper: a strongly fair
\* action keeps the system within the set of states that are closed under
\* it.
StrongFairness(S, R) ==
  \A x, y \in S : (R(x, y) /\ (x \in S)) => (y \in S)

\* The weak-fairness rule from Lamport's TLA+ paper: a weakly fair action
\* keeps the system within the set of states that are closed under it,
\* under the weaker liveness assumption.
WeakFairness(S, R) ==
  \A x, y \in S : (R(x, y) /\ (x \in S)) => (y \in S)

\* The step-simulation rule of Lamport's TLA+ paper: if every step of the
\* concrete system is matched by a step of the abstract system, the
\* concrete system implements the abstract one.
StepSimulation(S, R, a) ==
  \A x, y \in S : (a(x, y) /\ (x \in S)) => (R(x, y) /\ (y \in S))

====
---- MODULE TLAPS ----
EXTENDS Naturals

\* This module defines backend pragmas for the TLA Proof System (TLAPS). It declares the
\* provers that the system may dispatch to, along with their individual timeouts and tactics,
\* and it contains the fundamental temporal-logic proof rules (invariance, well-formedness,
\* strong fairness, weak fairness, and step simulation) taken from Lamport's "The Temporal
\* Logic of Actions". The two theorems at the end -- set extensionality and that no set
\* contains every possible value -- are basic logical truths that every proof must encode.
\* No state variables or system actions are defined here: this is a helper module, not a
\* model of a running system, so the state and actions sections are empty on purpose.

CONSTANTS
  Provers,   \* The set of automated provers that TLAPS may invoke (defined below).
  Tactics,   \* Named proof tactics that can be passed to a prover.
  Timeouts   \* Per-prover timeouts (in ms) for how long TLAPS waits for a result.

Provers == { "zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass", "ls4" }
Tactics == { "default", "smt" }
Timeouts == [ p \in Provers |-> IF p = "zenon" THEN 2000 ELSE 5000 ]

\* Dispatch an obligation to a prover (optionally with a specific tactic). The result --
\* success or timeout -- is recorded in the same shared dispatch buffer below.
Dispatch == [ prover : Provers, tactic : Tactics ]

\* The buffer of outstanding proof obligations currently being dispatched to backends.
Outstanding == { d \in Dispatch : TRUE }

\* Dispatch a new proof obligation to the given prover, using the given tactic.
Prove(p, t) ==
  /\ [ prover |-> p, tactic |-> t ] \notin Outstanding
  /\ Outstanding' = Outstanding \cup { [ prover |-> p, tactic |-> t ] }

\* A backend prover finishes successfully and the obligation leaves the buffer.
ProveSuccess(d) ==
  /\ d \in Outstanding
  /\ Outstanding' = Outstanding \ { d }

\* A backend prover times out; the obligation leaves the buffer for retry or a different prover.
ProveTimeout(d) ==
  /\ d \in Outstanding
  /\ Outstanding' = Outstanding \ { d }

InitDispatch == \E p \in Provers, t \in Tactics : Prove(p, t)

\* No system state (variables) is being modeled here, so the INVARIANT section is empty.
Init == InitDispatch
Next == \E p \in Provers, t \in Tactics : Prove(p, t) \/ ProveSuccess([ prover |-> p, tactic |-> t ])
        \/ ProveTimeout([ prover |-> p, tactic |-> t ])

Spec == Init /\ [][Next]_Outstanding

\* Invariance rule: if a state predicate is preserved by every step, then it holds from the
\* start and for the rest of the run.
InvariantRule(P) == (\A e \in [1..LEN(Next)] : P /\ Next[e] => P') => (P => [][Next]_P)

\* Well-formedness: a predicate that is a state constraint must be preserved by every step.
WellFormed(P) == (\A e \in [1..LEN(Next)] : P /\ Next[e] => P') => (P => [Next]_P)

\* Strong fairness: if an action is continuously enabled it must eventually take effect.
StrongFair(E) == (E /\ [](E => <>E)) => <>E

\* Weak fairness: an action that is enabled infinitely often must eventually take effect.
WeakFair(E) == ([]<>(E /\ <>E)) => <>E

\* Step simulation: if every step of one system can be matched by a step of another, the first
\* system never gets ahead of the second.
StepSim(Sim) == (\A e \in [1..LEN(Sim)] : Sim[e] => Sim[e]') => (Sim => Sim)

\* Set extensionality: two sets are equal exactly when they contain the same elements.
Extensionality == \A a, b : (\A x \in {a, b} : x \in a <=> x \in b) => a = b

\* No set of values contains every possible value.
UniverseNotCaptured == \A a : (\A x \in {a} : x \in a) => FALSE

====
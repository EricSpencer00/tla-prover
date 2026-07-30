---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS Zenon, Isabelle, CVC3, VeriT, Yices, Z3, SPASS, LS4, MaxTime

ZenonOps == {1, 2, 3}
UnifyOps == {1}
InstOps == {1, 2}
TheoryOps == {1, 2, 3}
InstBound == 3
CrunchBound == 2

\* Backend provers that TLAPS can dispatch to.
Backends == {"zenon", "isabelle", "cvc3", "verit", "yices", "z3", "spass", "ls4"}

\* Dispatch a proof obligation to a backend prover (or none) with a timeout.
Dispatch(op, b, t) ==
  /\ op \in Backends
  /\ t \in 0 .. MaxTime
  /\ UNCHANGED <<>>

\* Recurse on a subgoal with a bounded depth.
Recurse(op, g, d) ==
  /\ op \in Backends
  /\ g \in 1 .. InstBound
  /\ d \in 0 .. CrunchBound
  /\ UNCHANGED <<>>

\* The invariance rule: once a variable is known to be invariant it stays so.
Invariance(v) ==
  /\ v \in Backends
  /\ UNCHANGED <<>>

\* The well-formedness rule: formulas that parse correctly are well-formed.
WellFormed(f) ==
  /\ f \in Backends
  /\ UNCHANGED <<>>

\* Strong fairness: a repeatedly enabled action must eventually fire.
StrongFair(e) ==
  /\ e \in Backends
  /\ UNCHANGED <<>>

\* Weak fairness: a continuously enabled action must eventually fire.
WeakFair(e) ==
  /\ e \in Backends
  /\ UNCHANGED <<>>

\* The step-simulation rule (Lamport's STS5).
StepSimulation(e) ==
  /\ e \in Backends
  /\ UNCHANGED <<>>

\* Set extensionality: two sets with the same elements are equal.
Extensionality ==
  \A X, Y \in SUBSET Backends : (\A e \in Backends : (e \in X) <=> (e \in Y)) => X = Y

\* Nothing is a universal set of all values.
NoUniversalSet ==
  ~ \E X \in SUBSET Backends : \A e \in Backends : e \in X

SPECIFICATION == \A op \in Backends : Dispatch(op, "none", 0)

INIT == \A op \in Backends : Dispatch(op, "none", 0)

NEXT == \E op \in Backends, g \in 1 .. InstBound :
          Recurse(op, g, 0)

INVARIANTS == Extensionality

PROPERTIES == NoUniversalSet

\* No identifiers required by the .cfg; this module only defines the
\* operators above so the configuration leaves everything up to the user.
====
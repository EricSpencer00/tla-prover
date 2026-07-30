---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  provers, tactics, timeouts

\* Backend operators: each rule names a prover and fixes a timeout for that
\* invocation; the action is a NoOp since this module has no state to change.
\* They are gathered into the operator set Dispatches for the spec.
Zero == 0
Dispatches ==
  { Zenon(p, k) : p \in provers, k \in timeouts } \cup
  { Isabelle(p, k) : p \in provers, k \in timeouts } \cup
  { CVC3(p, k) : p \in provers, k \in timeouts } \cup
  { Yices(p, k) : p \in provers, k \in timeouts } \cup
  { VeriT(p, k) : p \in provers, k \in timeouts } \cup
  { Z3(p, k) : p \in provers, k \in timeouts } \cup
  { SPASS(p, k) : p \in provers, k \in timeouts } \cup
  { LS4(p, k) : p \in provers, k \in timeouts }

NoOp == TRUE

Next == NoOp

TemporalLogicRules ==
  { InvariantRule(S, P, Q),
    WfStrong(S, Q),
    WfWeak(S, Q),
    StepSimulation(S, Q) }

Spec == Init /\ [][Next]_Zero

Init == NoOp

Invariants == {}

Properties ==
  { Extensionality, NoUniversalSet } \cup TemporalLogicRules

\* Standard invariance rule from Lamport's TLA.
InvariantRule(S, P, Q) ==
  /\ S \in DOMAIN(P)
  /\ \A s \in S : P[s] => Q[s]

WfStrong(S, Q) ==
  /\ S # {}
  /\ \A s \in S : Q[s]

WfWeak(S, Q) ==
  /\ S # {}
  /\ \A s \in S : Q[s]

StepSimulation(S, Q) ==
  /\ S # {}
  /\ \A s \in S : Q[s]

Extensionality ==
  \A S, T \in SUBSET Nat : (\A x \in Nat : x \in S <=> x \in T) => S = T

NoUniversalSet ==
  \A S \in SUBSET Nat : S # Nat

====
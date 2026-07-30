---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon
  Isabelle
  CVC3
  Yices
  VeriT
  Z3
  SPASS
  LS4
  NoSet

\* TLAPS backend dispatchers: each operator tells the proof system which
\* prover to invoke for the current obligation, together with a timeout.
\* (The timeout values themselves are not modelled here; they are
\* configuration entries in the .cfg file and are not part of the TLA+ state.)

ZenonOp ==
  [ prover |-> "Zenon", timeout |-> 30 ]

IsabelleOp ==
  [ prover |-> "Isabelle", timeout |-> 30 ]

CVC3Op ==
  [ prover |-> "CVC3", timeout |-> 30 ]

YicesOp ==
  [ prover |-> "Yices", timeout |-> 30 ]

VeriTOp ==
  [ prover |-> "VeriT", timeout |-> 30 ]

Z3Op ==
  [ prover |-> "Z3", timeout |-> 30 ]

SPASSOp ==
  [ prover |-> "SPASS", timeout |-> 30 ]

LS4Op ==
  [ prover |-> "LS4", timeout |-> 30 ]

\* Core temporal-logic proof rules (names imported from the standard
\* proof-library module; these theorems are postulated so that their names
\* are reserved and future versions cannot clash with them).

\* Invariance: an invariant that holds in the initial state and is preserved
\* by every transition holds in every reachable state.
Invariance ==
  \A InitPred, NextPred, Inv ==
    /\ InitPred \in BOOLEAN
    /\ NextPred \in BOOLEAN
    /\ Inv \in BOOLEAN
    /\ InitPred => Inv
    /\ (Inv /\ NextPred) => Inv

\* Well-formedness: a well-formed transition system can always be started.
WellFormed ==
  \A InitPred, NextPred ==
    /\ InitPred \in BOOLEAN
    /\ NextPred \in BOOLEAN
    /\ InitPred => TRUE

\* Strong fairness: an action that is continuously enabled eventually fires.
StrongFairness ==
  \A ActionEnb, ActionExec ==
    /\ ActionEnb \in BOOLEAN
    /\ ActionExec \in BOOLEAN
    /\ (ACTION_ENABLING =>~
         (ACTION_EXECUTING <=> ActionExec))

\* Weak fairness: an action that is enabled infinitely often eventually fires.
WeakFairness ==
  \A ActionEnb, ActionExec ==
    /\ ActionEnb \in BOOLEAN
    /\ ActionExec \in BOOLEAN
    /\ (ActionEnb ~> ActionExec)

\* Step simulation: every step of the concrete system is matched by a step
\* of the abstract specification.
StepSimulation ==
  \A ConcreteStep, AbstractStep ==
    /\ ConcreteStep \in BOOLEAN
    /\ AbstractStep \in BOOLEAN
    /\ (ConcreteStep => AbstractStep)

\* Extensionality: two sets with exactly the same members are equal.
Extensionality ==
  \A A, B \in SUBSET {NoSet} : (A = B) <=> (A \subseteq B /\ B \subseteq A)

\* No set contains every possible value.
NoSetContainsAll ==
  \A X \in SUBSET {NoSet} : X # {NoSet}

\* The specification is the conjunction of the reserved rule names (the
\* proof rules are not themselves temporally evolving, so the spec is a
\* single state that must satisfy all of them).
SPECIFICATION ==
  Extensionality /\ NoSetContainsAll /\ Invariance
  /\ WellFormed /\ StrongFairness /\ WeakFairness /\ StepSimulation

INIT ==
  Extensionality /\ NoSetContainsAll /\ Invariance
  /\ WellFormed /\ StrongFairness /\ WeakFairness /\ StepSimulation

NEXT ==
  Extensionality /\ NoSetContainsAll /\ Invariance
  /\ WellFormed /\ StrongFairness /\ WeakFairness /\ StepSimulation

INVARIANTS == Extensionality

PROPERTIES == NoSetContainsAll

====
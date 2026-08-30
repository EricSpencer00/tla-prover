---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, NoTimeout

\* These are the backend provers TLAPS can invoke.  The array holds each
\* prover together with the amount of time the proof manager will wait
\* for it before giving up on that branch of the proof.
Backends == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4}

VARIABLES backends, timeout, ipc

Vars == <<backends, timeout, ipc>>

TypeOK ==
  /\ backends \subseteq Backends
  /\ timeout \in {NoTimeout} \union (0..2)
  /\ ipc \in {"free", "held"}

Init ==
  /\ backends = {}
  /\ timeout = NoTimeout
  /\ ipc = "free"

\* The proof manager hands a backend prover the shared proof-log lock.
Acquire(b) ==
  /\ b \notin backends
  /\ ipc = "free"
  /\ backends' = backends \union {b}
  /\ ipc' = "held"
  /\ UNCHANGED timeout

Release(b) ==
  /\ b \in backends
  /\ backends' = backends \ {b}
  /\ ipc' = "free"
  /\ UNCHANGED timeout

SetTimeout(v) ==
  /\ timeout = NoTimeout
  /\ timeout' = v
  /\ UNCHANGED <<backends, ipc>>

\* The proof manager gives up on a backend that is running too slowly.
Timeout ==
  /\ timeout # NoTimeout
  /\ backends' = {}
  /\ timeout' = NoTimeout
  /\ ipc' = "free"

Next ==
  \/ \E b \in Backends : Acquire(b)
  \/ \E b \in Backends : Release(b)
  \/ \E v \in 0..2 : SetTimeout(v)
  \/ Timeout

Spec ==
  /\ Init
  /\ [][Next]_Vars

\* Two basic set-theoretic facts that the rest of the proof library builds
\* on: set extensionality and the fact that no set can contain everything.
ExtensionalityUsed == TRUE
NoUniversalSetUsed == TRUE

\* The invariance rule: a state predicate that is preserved every time a
\* transition is taken is true in every reachable state.
\* The well-formedness rules: a temporal formula must have its subformulas
\* well formed before it can be asserted.
\* Strong fairness: an action that is enabled infinitely often is taken
\* infinitely often.  Weak fairness: an action that is enabled forever is
\* eventually taken.  Step simulation: every transition of the system has
\* a corresponding transition in its abstract specification.
\* (These are quoted from Lamport's 'The Temporal Logic of Actions'.)
\* They are included here so that their names are reserved and cannot be
\* inadvertently reused in a later version of the library.
InvarianceRule == TRUE
WellFormednessRule == TRUE
StrongFairnessRule == TRUE
WeakFairnessRule == TRUE
StepSimulationRule == TRUE

SpecProps == {InvarianceRule, WellFormednessRule, StrongFairnessRule,
  WeakFairnessRule, StepSimulationRule}

====
---- MODULE TLAPS ----
EXTENDS Naturals

(* Deployable prover backends: each is an operator the proof system may    *)
(* invoke on a proof obligation, parameterized by a timeout.              *)
Zenon(k)    == [backend |-> "zenon",    timeout |-> k]
Isabelle(k) == [backend |-> "isabelle", timeout |-> k]
CVC3(k)     == [backend |-> "cvc3",     timeout |-> k]
Yices(k)    == [backend |-> "yices",    timeout |-> k]
VeriT(k)    == [backend |-> "verit",    timeout |-> k]
Z3(k)       == [backend |-> "z3",       timeout |-> k]
SPASS(k)    == [backend |-> "spass",    timeout |-> k]
LS4(k)      == [backend |-> "ls4",      timeout |-> k]

(* Temporal proof rules from Lamport's TLA+ paper, included here so their *)
(* names are reserved and unavailable for other definitions.              *)
Invariance(rule) == "rule " /\ rule
WellFormed    == "rule wellformed"
StrongFair    == "rule strongfair"
WeakFair      == "rule weakfair"
StepSim       == "rule stepsim"

CONSTANTS
  CONSTANTS

\* Specification: the set of prover/timeout configurations that TLAPS may *
\* deploy for a given proof obligation.                                    *
Specification == { Zenon(1), Isabelle(1), LS4(2), Yices(1), Z3(2) }

Init == TRUE

Next == Init

Spec == Init /\ [][Next]_Init

Theorems == { "sets with the same elements are equal", "no set contains every value" }

====
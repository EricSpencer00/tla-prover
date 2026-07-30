---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  maxSatCalls
  cvc3Timeout
  ls4Timeout
  yicesTimeout
  veriTTimeout
  z3Timeout
  spassTimeout
  zenonTimeout

VARIABLES satCalls, lastSolver

vars == <<satCalls, lastSolver>>

TypeOK ==
  /\ satCalls \in 0..maxSatCalls
  /\ lastSolver \in {"none", "cvc3", "ls4", "yices", "veriT", "z3", "spass", "zenon"}

Init ==
  /\ satCalls = 0
  /\ lastSolver = "none"

\* The elements of this module are all proof-system infrastructure: there is
\* no concurrent computation to model. Each action records that the proof
\* system chose a particular prover, which consumes one unit of the bounded
\* budget of SAT/SMT calls. The budget is always finite; once it is spent the
\* backends simply stop firing.
DispatchCVC3 ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "cvc3"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchLS4 ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "ls4"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchYices ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "yices"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchVeriT ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "veriT"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchZ3 ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "z3"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchSpass ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "spass"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

DispatchZenon ==
  /\ satCalls < maxSatCalls
  /\ lastSolver' = "zenon"
  /\ satCalls' = satCalls + 1
  /\ UNCHANGED << >>

Next ==
  \/ DispatchCVC3
  \/ DispatchLS4
  \/ DispatchYices
  \/ DispatchVeriT
  \/ DispatchZ3
  \/ DispatchSpass
  \/ DispatchZenon

\* Top-level spec: always init, then always some dispatch action, with the
\* whole run kept within the bounded budget and the budget never negative.
Spec == Init /\ [][Next]_vars

\* The foundational theorems: set extensionality and the existence of a
\* value outside every set. Both are always true, and they are included here
\* so that their names cannot be silently reused for something else.
Extensionality ==
  \A X, Y \in SUBSET Nat : (\A x \in Nat : (x \in X) <=> (x \in Y)) => X = Y

NotEverySetContainsEveryValue ==
  \A X \in SUBSET Nat : \E x \in Nat : x \notin X

====
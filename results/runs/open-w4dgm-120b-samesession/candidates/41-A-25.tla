---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,         \* the set of processes in the system
  d0,           \* default timeout interval for all processes
  SendPoint,    \* sends happen when the local clock is a multiple of this
  PredictPoint, \* predictions happen when the local clock is a multiple of this
  Messages      \* the set of alive messages (one per ordered sender/receiver pair)

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # 0 /\ PredictPoint # 0 /\ SendPoint # PredictPoint

\* A message is a sender/receiver pair of distinct processes
Message == {m \in Messages : m[1] # m[2]}
RECURSIVE SumOf(_, _)
SumOf(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN f[x] + SumOf(f, S \ {x})

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> Nat]
  /\ suspect \subseteq (Proc \X Proc)
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = {}
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

\* Send an alive message to every other process (clock at a SendPoint multiple)
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup {<<p, q>> : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0
                                                    ELSE IF lastHeard[p][q] < timeout[p] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

\* Predict that any not-yet-heard process has crashed (clock at a PredictPoint multiple)
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = suspect \cup {<<p, q>> : q \in Proc \ {p} /\ lastHeard[p][q] > timeout[p]}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0
                                                    ELSE IF lastHeard[p][q] < timeout[p] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive messages; receiving traffic for a suspected process adapts its timeout
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E msgs \in SUBSET Message :
       /\ \A m \in msgs : m \in outbox /\ m[2] = p
       /\ outbox' = outbox \ msgs
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                              IF <<q, p>> \in msgs THEN 0
                              ELSE IF lastHeard[p][q] < timeout[p] THEN @ + 1 ELSE @]]
       /\ suspect' = suspect \ {[p, q] \in suspect : <<q, p>> \in msgs}
       /\ timeout' = [timeout EXCEPT ![p] = IF \E q \in Proc : <<q, p>> \in msgs /\ lastHeard[p][q] > timeout[p]
                                             THEN timeout[p] + 1 ELSE timeout[p]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]

RotateClock(p) ==
  /\ clock[p]' = IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ clock[p] > timeout[p]
                 THEN 0 ELSE clock[p]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : RotateClock(p)

Spec == Init /\ [][Next]_vars

\* The process-local timeout intervals always sum to a finite amount bounded
\* by the number of processes; this keeps the model finite-state for TLC.
TimeoutBound == SumOf(timeout, Proc) <= Cardinality(Proc) * timeout[CHOOSE p \in Proc : TRUE]
====
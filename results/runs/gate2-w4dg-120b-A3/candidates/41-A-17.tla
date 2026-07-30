---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ SendPoint >= 1 /\ PredictPoint \in Nat /\ PredictPoint >= 1
ASSUME SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES suspectSet, timeout, lastHeard, pc, outbox

vars == <<suspectSet, timeout, lastHeard, pc, outbox>>

TypeOK ==
  /\ suspectSet \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ pc \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspectSet = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ pc = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* A process sends out alive messages to every other process.
SendAlive(p) ==
  /\ pc[p] % SendPoint = 0
  /\ pc[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q = p \/ q \in suspectSet[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<suspectSet, timeout>>

\* A process suspects anyone it hasn't heard from beyond that process's timeout.
Predict(p) ==
  /\ pc[p] % PredictPoint = 0
  /\ pc[p] % SendPoint # 0
  /\ suspectSet' = [suspectSet EXCEPT ![p] = suspectSet[p] \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q = p \/ q \in suspectSet[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Receiving an alive message resets the counter and clears the suspicion.
Receive(p) ==
  /\ pc[p] % SendPoint # 0 \/ pc[p] % PredictPoint # 0
  /\ \E w \in outbox[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![w.from] = 0]
       /\ suspectSet' = [suspectSet EXCEPT ![p] = suspectSet[p] \ {w.from}]
       /\ timeout' = [timeout EXCEPT ![w.from] = IF w.from \in suspectSet[p] THEN timeout[w.from] + 1 ELSE timeout[w.from]]
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {w}]
  /\ pc' = [pc EXCEPT ![p] = pc[p] + 1]

Reset(p) ==
  /\ pc[p] > SendPoint
  /\ pc[p] > PredictPoint
  /\ \A q \in Proc : pc[p] > timeout[q]
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspectSet, timeout, lastHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : Reset(p)

Spec == Init /\ [][Next]_vars

====
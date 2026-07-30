---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES timeout, lastHeard, suspicion, clock, outbox

vars == <<timeout, lastHeard, suspicion, clock, outbox>>

\* Sets are used in place of booleans for cross-process messages.
MsgSpace == Messages \X [sender: Proc, receiver: Proc]

TypeOK ==
  /\ \A p \in Proc : \A q \in Proc : timeout[p][q] \in Nat
  /\ \A p \in Proc : \A q \in Proc : lastHeard[p][q] \in Nat
  /\ \A p \in Proc : suspicion[p] \subseteq Proc
  /\ \A p \in Proc : clock[p] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq MsgSpace

\* Initializing every lastHeard counter to zero models a state in which all
\* processes are known to be recently alive.
Init ==
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ suspicion = [p \in Proc |-> {}]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in MsgSpace : m.receiver \in Proc /\ m.sender = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in outbox[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, suspicion>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc : lastHeard[p][q] >= timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> lastHeard[p][q] + 1]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF (\E m \in outbox[q] : m.receiver = p) THEN 0 ELSE lastHeard[p][q]]]
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc : ~(\E m \in outbox[q] : m.receiver = p)}]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
                    IF (\E m \in outbox[q] : m.receiver = p) /\ lastHeard[p][q] >= timeout[p][q]
                      THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ clock' = [clock EXCEPT ![p] =
                 IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint /\ \A q \in Proc : clock[p] >= timeout[p][q]
                   THEN 0 ELSE clock[p]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Proc : SendAlive(p))
  /\ WF_vars(\E p \in Proc : Predict(p))

====
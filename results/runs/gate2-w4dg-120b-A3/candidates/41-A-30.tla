---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspectSet, timeout, lastHeard, outbox

vars == <<clock, suspectSet, timeout, lastHeard, outbox>>

\* Each process sends alive messages on a bounded clock; the clock is local to
\* the process, and its domain is truncated rather than unbounded (a single
\* reset once it passes every relevant threshold).
TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ suspectSet \subseteq [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspectSet = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] > 0
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.receiver \in Proc}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
      IF q = p \/ q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspectSet, timeout>>

Predict(p) ==
  /\ clock[p] > 0
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspectSet' = [suspectSet EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF lastHeard[p][q] >= timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receiving only touches the sender's own timer and suspicion set; the sender
\* keeps its own outbox and clock, so it cannot be forced into the same tick.
Receive(p) ==
  /\ clock[p] > 0
  /\ outbox[p] # {}
  /\ \E m \in outbox[p] :
        /\ suspectSet' = [suspectSet EXCEPT ![p] = @ \ {m.receiver}]
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.receiver] = 0]
        /\ timeout' = [timeout EXCEPT ![p][m.receiver] =
            IF m.receiver \in suspectSet[p] THEN @ + 1 ELSE @]
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m \in outbox[p] : m.receiver = p}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
                                      /\ \A q \in Proc : clock[p] + 1 > timeout[p][q]
                                      THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars

====
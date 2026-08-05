---- MODULE EPFailureDetector ----
EXTENDS Integers, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint # PredictPoint

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

OtherOf(p) == {q \in Proc : q # p}

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> INTEGER]
  /\ lastHeard \in [Proc -> [OtherOf(<< >>) -> INTEGER]]
  /\ clock \in [Proc -> INTEGER]
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> [q \in OtherOf(<< >>) |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup { [to |-> q, from |-> p] : q \in OtherOf(<< >>) }
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in OtherOf(<< >>) |-> IF lastHeard[p][q] < timeout[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in OtherOf(<< >>) : lastHeard[p][q] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in OtherOf(<< >>) |-> IF lastHeard[p][q] < timeout[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox :
       /\ m.to = p
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
       /\ timeout' = [timeout EXCEPT ![m.from] = IF m.from \in suspect[p] THEN timeout[m.from] + 1 ELSE timeout[m.from]]
       /\ outbox' = outbox \ {m}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

Reset(p) ==
  /\ clock[p] > SendPoint /\ clock[p] > PredictPoint /\ \A d \in OtherOf(<< >>) : clock[p] > timeout[d]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : Reset(p)

Spec == Init /\ [][Next]_vars

====
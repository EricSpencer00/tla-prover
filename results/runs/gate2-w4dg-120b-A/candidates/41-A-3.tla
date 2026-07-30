---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ PredictPoint \in Nat
       /\ SendPoint > 0 /\ PredictPoint > 0
       /\ \A n \in Nat : ~(SendPoint = n * PredictPoint)
       /\ \A n \in Nat : ~(PredictPoint = n * SendPoint)

VARIABLES suspicion, timeout, lastHeard, localTime, outgoing

vars == <<suspicion, timeout, lastHeard, localTime, outgoing>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ localTime \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ localTime = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ localTime[p] % SendPoint = 0
  /\ localTime[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages :
                                          /\ m.src = p
                                          /\ m.dst \in Proc \ {p}}]
  /\ localTime' = [localTime EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
                    IF q \in outgoing[p].dst /\ lastHeard[q] < timeout[q]
                    THEN lastHeard[q] + 1
                    ELSE lastHeard[q]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ localTime[p] % PredictPoint = 0
  /\ localTime[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
                     @ \cup {q \in Proc :
                       lastHeard[q] >= timeout[q] /\ q # p}]
  /\ lastHeard' = [q \in Proc |->
                    IF lastHeard[q] < timeout[q]
                    THEN lastHeard[q] + 1
                    ELSE lastHeard[q]]
  /\ localTime' = [localTime EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outgoing>>

ResetClock(p) ==
  /\ localTime[p] > SendPoint /\ localTime[p] > PredictPoint
  /\ \A q \in Proc : localTime[p] > timeout[q]
  /\ localTime' = [localTime EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspicion, timeout, lastHeard, outgoing>>

Receive(p) ==
  /\ localTime' = [localTime EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
                    IF q \in Proc \ {p} /\ lastHeard[q] < timeout[q]
                    THEN lastHeard[q] + 1
                    ELSE lastHeard[q]]
  /\ suspicion' = [q \in Proc |->
                     IF p \in suspicion[q] /\ p \in {m.dst : m \in outgoing[q]}
                     THEN suspicion[q] \ {p}
                     ELSE suspicion[q]]
  /\ timeout' = [q \in Proc |->
                   IF p \in suspicion[q] /\ p \in {m.dst : m \in outgoing[q]}
                   THEN timeout[q] + 1
                   ELSE timeout[q]]
  /\ UNCHANGED <<outgoing>>

Next_ ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next_]_vars

====
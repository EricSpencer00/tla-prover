---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process acts as its own sender and receiver, with an adaptive
\* failure detector: it predicts crashes only after a timeout of silence.
VARIABLES suspect, timeout, lastHeard, local, outgoing

vars == <<suspect, timeout, lastHeard, local, outgoing>>


MsgSpace == [to : Proc, from : Proc]

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ local \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ local = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

\* Send alive messages at multiples of SendPoint, but never at the same
\* instant as a predict, so sending and predicting never overlap.
SendAlive(p) ==
  /\ local[p] % SendPoint = 0
  /\ local[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.to \in Proc /\ m.from = p}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ local' = [local EXCEPT ![p] = local[p] + 1]
  /\ suspect' = suspect
  /\ timeout' = timeout

MakePrediction(p) ==
  /\ local[p] % PredictPoint = 0
  /\ local[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q]
                                                    THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ local' = [local EXCEPT ![p] = local[p] + 1]
  /\ outgoing' = outgoing
  /\ timeout' = timeout

Receive(p) ==
  /\ local[p] % SendPoint # 0
  /\ local[p] % PredictPoint # 0
  /\ \E m \in outgoing[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
       /\ timeout' = [timeout EXCEPT ![p][m.from] = @ + (IF m.from \in suspect[p] THEN 1 ELSE 0)]
  /\ local' = [local EXCEPT ![p] = local[p] + 1]
  /\ outgoing' = [outgoing EXCEPT ![p] = {}]

ClockReset(p) ==
  /\ local[p] > SendPoint \/ local[p] > PredictPoint
     \/ \E q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]
  /\ local' = [local EXCEPT ![p] = 0]
  /\ suspect' = suspect
  /\ timeout' = timeout
  /\ lastHeard' = lastHeard
  /\ outgoing' = outgoing

Next == \E p \in Proc : SendAlive(p) \/ MakePrediction(p) \/ Receive(p) \/ ClockReset(p)

Spec == Init /\ [][Next]_vars

====
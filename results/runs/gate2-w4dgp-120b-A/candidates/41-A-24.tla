---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat
       /\ PredictPoint \in Nat
       /\ SendPoint # 0
       /\ PredictPoint # 0
       /\ SendPoint # PredictPoint
       /\ d0 \in Nat
       /\ d0 > 0

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dest \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc \ {p} |-> IF lastHeard[p][q] < timeout[p][q]
                           THEN lastHeard[p][q] + 1
                           ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        suspect[p] \cup
        {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc \ {p} |-> IF lastHeard[p][q] < timeout[p][q]
                           THEN lastHeard[p][q] + 1
                           ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
       /\ clock[p] < timeout[p][m.dest]
       /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [lastHeard[p] EXCEPT ![m.dest] = 0]]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.dest}]
       /\ timeout' = [timeout EXCEPT ![p] =
            [timeout[p] EXCEPT
              [m.dest] = IF m.dest \in suspect[p] THEN timeout[p][m.dest] + 1
                         ELSE timeout[p][m.dest]]]
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

ResetClock(p) ==
  /\ clock[p] >= SendPoint
  /\ clock[p] >= PredictPoint
  /\ \A q \in Proc \ {p} : clock[p] >= timeout[p][q]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]

====
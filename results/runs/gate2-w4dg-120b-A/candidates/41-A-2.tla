---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ (SendPoint < PredictPoint => PredictPoint % SendPoint # 0)
       /\ (PredictPoint < SendPoint => SendPoint % PredictPoint # 0)

VARIABLES suspect, timeout, lastHeard, clock, outbox
vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* Each process acts independently on its own clock; messages are sent
\* toward a process and received from it, so suspect/heard/timeout are
\* indexed in the same order.
SentTo == [from: Proc, to: Proc, kind: {"alive"}]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {[from |-> p, to |-> q, kind |-> "alive"] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : q # p /\ lastHeard[p][q] >= timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ \E m \in Messages :
       /\ m.kind = "alive"
       /\ m.to = p
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
       /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN timeout[p][m.from] + 1 ELSE timeout[p][m.from]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ \A q \in Proc : clock[p] > timeout[p][q] THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED outbox

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET SentTo]

====
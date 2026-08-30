---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Process-local state: suspicion, timeout interval per peer, last-heard
\* counters, local clock, and the outgoing messages this process wants to
\* push.  The send and predict steps never fire at the same clock value.
VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outbox \subseteq Messages

MaxT == CHOOSE t \in timeout : \A q \in Proc : timeout[q] <= t

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

\* Send alive messages to everyone.
Send(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup {m \in Messages : m.from = p}
  /\ lastHeard' = [q \in Proc |-> IF q \notin outbox \cup {m \in Messages : m.from = p} THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<suspicion, timeout>>

\* Predict a crash for any peer that has timed out.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ lastHeard' = [q \in Proc |-> IF q \notin outbox \cup {m \in Messages : m.from = p} THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Every other clock value: receive and possibly adjust an adaptive timeout.
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ lastHeard' = [q \in Proc |-> IF \E m \in outbox : m.from = q THEN 0 ELSE IF q \notin outbox THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ suspicion' = [q \in Proc |-> IF q \in outbox THEN suspicion[p] \ {q} ELSE suspicion[p]]
  /\ timeout' = [q \in Proc |-> IF q \in outbox /\ q \in suspicion THEN @ + 1 ELSE @]
  /\ outbox' = outbox \ {m \in outbox : m.from \in Proc}
  /\ clock' = IF clock[p] > MaxT /\ \A q \in Proc : clock[q] > MaxT
                THEN [clock EXCEPT ![p] = 0]
                ELSE [clock EXCEPT ![p] = @ + 1]

Next ==
  \/ \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
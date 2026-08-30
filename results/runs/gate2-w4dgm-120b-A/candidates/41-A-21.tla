---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ \A p \in Proc : suspect[p] \subseteq Proc /\ lastHeard[p] \in [Proc -> 0..d0]
  /\ \A p \in Proc : timeout[p] \in [Proc -> 1..d0]
  /\ clock \in [Proc -> 0..d0]
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> 1]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

\* Sending and predicting are driven by separate clocks so they never coincide.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outbox' = {m \in outbox : m.from # p}
       \cup { [from |-> p, to |-> q] : q \in Proc \ {p} }
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ q \in suspect[p] \/ lastHeard[p][q] >= timeout[p][q]
          THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspect' = [p \in Proc |->
        IF p = p \/ \E q \in Proc : lastHeard[p][q] > timeout[p][q]
          THEN suspect[p] \cup {q}
          ELSE suspect[p]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ q \in suspect[p] \/ lastHeard[p][q] >= timeout[p][q]
          THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox :
       /\ m.to = p /\ m.from # p
       /\ outbox' = outbox \ {m}
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
       /\ timeout' = [q \in Proc |->
            IF q = m.from /\ m.from \in suspect[p]
              THEN LET d == timeout[p][q] + 1 IN IF d <= d0 THEN d ELSE d0
              ELSE timeout[p][q]]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] >= d0 THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====
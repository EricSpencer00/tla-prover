---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* An eventually perfect failure detector: correct processes send alive
\* messages and stop suspecting peers once they hear from them.
\* Timeout intervals adapt (grow) when a suspected process turns out to be
\* correct and sends thereafter; the safety invariant is type/coherence only.

VARIABLES suspected, timeout, lastHeard, clock, outbox

vars == <<suspected, timeout, lastHeard, clock, outbox>>

AliveOf == [dest : Proc, src : Proc]

Init ==
  /\ suspected = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Process p sends alive messages to every other process on its send schedule.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT
                  ![p] = {m \in outbox[p] : m.dest \notin Proc} \cup
                           { [dest |-> q, src |-> p] : q \in Proc, q # p }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT
                     ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q]
                                                 THEN lastHeard[p][q]
                                                 ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<suspected, timeout>>

\* Process p predicts based on its local per-peer clocks: it suspects any
\* peer from which it has not heard for longer than that peer's timeout.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspected' = [suspected EXCEPT
                     ![p] = {q \in Proc : q # p /\ lastHeard[p][q] >= timeout[p][q] \/ q \in suspected[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT
                     ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q]
                                                 THEN lastHeard[p][q]
                                                 ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receiving an alive message both resets the silence clock and stops
\* suspecting that peer.  Responding to a suspected peer grows its timeout.
Receive(p, msgs) ==
  /\ msgs # {}
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ lastHeard' = [lastHeard EXCEPT
                     ![p] = [q \in Proc |->
                               IF q = p /\ lastHeard[p][q] < timeout[p][q]
                                  THEN lastHeard[p][q] + 1
                                  ELSE IF \E m \in msgs : m.dest = p /\ m.src = q
                                          THEN 0
                                          ELSE lastHeard[p][q]]]
  /\ suspected' = [suspected EXCEPT ![p] =
                     {q \in Proc : (q \in suspected[p] /\ ~ \E m \in msgs : m.dest = p /\ m.src = q)
                                   \/ (q # p /\ \E m \in msgs : m.dest = p /\ m.src = q)}]
  /\ timeout' = [timeout EXCEPT
                  ![p] = [q \in Proc |->
                             IF q # p /\ q \in suspected[p] /\ \E m \in msgs : m.dest = p /\ m.src = q
                                THEN timeout[p][q] + 1
                                ELSE timeout[p][q]]]
  /\ clock' = [clock EXCEPT ![p] =
                 IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
                     /\ \A q \in Proc : clock[p] + 1 <= timeout[p][q]
                 THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED <<outbox>>

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ \E msgs \in SUBSET {m \in outbox[p] : m.dest \in Proc} : Receive(p, msgs)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspected \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET {m \in Messages : m.dest \in Proc}]
====
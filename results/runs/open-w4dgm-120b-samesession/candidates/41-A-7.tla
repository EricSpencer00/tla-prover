---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send an alive message to every other process at a send tick; the clock is
\* bounded so sending and predicting never happen at the same tick.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {q \in Proc : q # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                         IF q # p /\ lastHeard[p][q] <= timeout[p][q]
                            THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

\* Predict at a predict tick which processes have timed out.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
                    suspect[p] \cup {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                         IF q # p /\ lastHeard[p][q] <= timeout[p][q]
                            THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive any incoming message, clearing suspicion and adapting timeouts.
Receive(p) ==
  /\ outbox' = [q \in Proc |->
                  IF q = p THEN {} ELSE outbox[q] \ {p}]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q \in Proc : q # p /\ q \in outbox[p]}]
  /\ timeout' = [timeout EXCEPT ![p] =
                    [q \in Proc |-> IF q # p /\ q \in outbox[p] /\ q \in suspect[p]
                                      THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-
                         IF q # p /\ q \in outbox[p] THEN 0 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint + PredictPoint + timeout[p][p]
                                      THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====
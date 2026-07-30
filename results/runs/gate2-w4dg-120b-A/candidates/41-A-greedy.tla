---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* A process sends alive messages at every multiple of SendPoint and makes
\* predictions at every multiple of PredictPoint; the two intervals never
\* coincide, so sending and predicting are always separate steps.
\* lastHeard[p][q] counts ticks since p last heard from q; timeout[p][q] is
\* the adaptive interval after which p suspects q.

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \subseteq [suspecter: Proc, suspectee: Proc]
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = {}
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = {m \in Messages : m.from = p}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = suspect \cup
       {[suspecter |-> p, suspectee |-> q] : q \in Proc :
          lastHeard[p][q] > timeout[p][q]}
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ suspect' = suspect \ {[suspecter |-> p, suspectee |-> q] : q \in Proc}
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF \E m \in outbox : m.from = q /\ m.to = p THEN 0 ELSE @]]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
        IF \E m \in outbox : m.from = q /\ m.to = p /\ [suspecter |-> p, suspectee |-> q] \in suspect
          THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > d0
                                      THEN 0 ELSE @ + 1]
  /\ UNCHANGED outbox

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====
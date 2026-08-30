---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

NONE == "none"

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* A process is suspected if its last-heard counter has exceeded that process's timeout.
SuspectProc(p, q) == (q \in suspect[p]) <=> (lastHeard[p][q] > timeout[p][q])

TypeOK ==
  /\ suspect \in [ Proc -> SUBSET Proc ]
  /\ timeout \in [ Proc -> [Proc -> Nat] ]
  /\ lastHeard \in [ Proc -> [Proc -> Nat] ]
  /\ clock \in [ Proc -> Nat ]
  /\ outbox \in [ Proc -> SUBSET Messages ]

Init ==
  /\ suspect = [ p \in Proc |-> {} ]
  /\ timeout = [ p \in Proc |-> [ q \in Proc |-> d0 ] ]
  /\ lastHeard = [ p \in Proc |-> [ q \in Proc |-> 0 ] ]
  /\ clock = [ p \in Proc |-> 0 ]
  /\ outbox = [ p \in Proc |-> {} ]

\* Send alive messages at every send tick, but never at a predict tick.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [ outbox EXCEPT ![p] = { m \in Messages : m.from = p } ]
  /\ clock' = [ clock EXCEPT ![p] = @ + 1 ]
  /\ lastHeard' = [ lastHeard EXCEPT ![p] =
       [ q \in Proc |->
           IF q = p \/ lastHeard[p][q] > timeout[p][q] THEN @
           ELSE @ + 1 ] ]
  /\ UNCHANGED << suspect, timeout >>

\* Make predictions at every predict tick, but never at a send tick.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [ suspect EXCEPT ![p] =
       suspect[p] \cup { q \in Proc : lastHeard[p][q] > timeout[p][q] } ]
  /\ clock' = [ clock EXCEPT ![p] = @ + 1 ]
  /\ lastHeard' = [ lastHeard EXCEPT ![p] =
       [ q \in Proc |->
           IF q = p \/ lastHeard[p][q] > timeout[p][q] THEN @
           ELSE @ + 1 ] ]
  /\ UNCHANGED << timeout, outbox >>

\* Receive messages at all other ticks; a message from a suspected process bumps its timeout.
Receive(p, m) ==
  /\ outbox[m.from] # {}
  /\ outbox' = [ outbox EXCEPT ![m.from] = @ \ {m} ]
  /\ lastHeard' = [ lastHeard EXCEPT ![p][m.from] = 0 ]
  /\ suspect' = [ suspect EXCEPT ![p] = suspect[p] \ {m.from} ]
  /\ timeout' = [ timeout EXCEPT ![p][m.from] =
       IF m.from \in suspect[p] THEN @ + 1 ELSE @ ]
  /\ UNCHANGED << clock, outbox >>

BustClock(p) ==
  /\ clock[p] > 0
  /\ \A q \in Proc : clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
  /\ \A q \in Proc : clock[p] > timeout[p][q]
  /\ clock' = [ clock EXCEPT ![p] = 0 ]
  /\ UNCHANGED << suspect, timeout, lastHeard, outbox >>

Next ==
  \E p \in Proc :
    \/ SendAlive(p) \/ Predict(p) \/ BustClock(p)
    \/ \E m \in Messages : Receive(p, m)

Spec == Init /\ [][Next]_vars

\* Every suspect link and its timeout are consistent with the process's view of liveness.
SuspicionsCoherent == \A p, q \in Proc : SuspectProc(p, q)

====
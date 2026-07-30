---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process separately maintains its own suspicion set, adaptive timeout
\* budget, last-heard counter, local clock, and outgoing message batch.

VARIABLES tclock, timeout, lastHeard, suspect, outgoing

vars == <<tclock, timeout, lastHeard, suspect, outgoing>>

None == "none"

TypeOK ==
  /\ tclock \in [Proc -> Nat]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ suspect \subseteq [suspectee: Proc, suspector: Proc]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ tclock = [p \in Proc |-> 0]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ suspect = {}
  /\ outgoing = [p \in Proc |-> {}]

InFlight(p) == \E m \in outgoing[p] : m.dest = p

SendAlive(p) ==
  /\ tclock[p] % SendPoint = 0
  /\ ~(tclock[p] % PredictPoint = 0)
  /\ outgoing' = [outgoing EXCEPT ![p] = {msg \in Messages : msg.dest # p}]
  /\ tclock' = [tclock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> [r \in Proc |->
       IF r \in suspect \cup {p} \cup {q} THEN lastHeard[p][r] ELSE lastHeard[p][r] + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ tclock[p] % PredictPoint = 0
  /\ ~(tclock[p] % SendPoint = 0)
  /\ suspect' = suspect \cup
       {s \in [suspectee: Proc, suspector: Proc] :
          /\ s.suspector = p
          /\ s.suspectee \notin suspect
          /\ lastHeard[p][s.suspectee] > timeout[p][s.suspectee]}
  /\ lastHeard' = [q \in Proc |-> [r \in Proc |->
       IF r # p THEN lastHeard[p][r] + 1 ELSE @]]
  /\ tclock' = [tclock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ ~(tclock[p] % SendPoint = 0 \/ tclock[p] % PredictPoint = 0)
  /\ \E m \in outgoing[p] : m.dest = p
  /\ lastHeard' = [q \in Proc |-> [r \in Proc |->
       IF r = m.source THEN 0
       ELSE IF r = p /\ [suspectee |-> r, suspector |-> q] \in suspect THEN @ + 1
       ELSE @]]
  /\ suspect' = suspect \ {[suspectee |-> m.source, suspector |-> p]}
  /\ timeout' = [q \in Proc |-> [r \in Proc |->
       IF r = m.source /\ [suspectee |-> r, suspector |-> q] \in suspect
       THEN timeout[q][r] + 1
       ELSE @]]
  /\ tclock' = [tclock EXCEPT ![p] = IF tclock[p] + 1 > SendPoint
                                      /\ tclock[p] + 1 > PredictPoint
                                      /\ tclock[p] + 1 > d0
                                      THEN 0 ELSE tclock[p] + 1]
  /\ outgoing' = [outgoing EXCEPT ![p] = outgoing[p] \ {m}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

\* Two structural invariants: last-heard counters are integers, and so are the
\* timeout budgets. The other invariants in the spec (TypeOK) cover the rest.
BoundedIntValues ==
  /\ \A p \in Proc : \A q \in Proc : lastHeard[p][q] \in Nat
  /\ \A p \in Proc : \A q \in Proc : timeout[p][q] \in Nat

====
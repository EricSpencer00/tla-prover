---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  d0,
  SendPoint,
  PredictPoint,
  Messages

N == Cardinality(Proc)

VARIABLES clock, suspect, timeout, lastHeard, outbox

vars == <<clock, suspect, timeout, lastHeard, outbox>>

\* For each process p, suspect[p] is its suspicion set; timeout[p][q] is
\* p's adaptive timeout for q, and lastHeard[p][q] is how many ticks ago p
\* heard from q. outbox[p] is the set of alive messages p intends to send.

TypeOK ==
  /\ clock \in [Proc -> 0..N]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> 1..N]]
  /\ lastHeard \in [Proc -> [Proc -> 0..N]]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = (Messages \cap [to : Proc]) \cup {x \in Messages : x.to = p}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ (clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0)
  /\ \E m \in outbox[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.to] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.to}]
       /\ timeout' = [timeout EXCEPT ![p][m.to] = IF m.to \in suspect[p] THEN timeout[p][m.to] + 1 ELSE timeout[p][m.to]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > N THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====
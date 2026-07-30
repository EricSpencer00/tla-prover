---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* The state captures, for each process, the set of processes it currently
\* suspects to have crashed, the adaptive timeout interval per peer, a counter
\* since it last heard from each peer, its local clock, and the set of
\* outgoing messages it wants to send. Send and predict are separated by the
\* clock two multiples that are never allowed to coincide.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint > 0 /\ PredictPoint > 0 /\ SendPoint # PredictPoint

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : outbox[p] \subseteq Messages
  /\ \A p \in Proc : clock[p] \in Nat

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

Transmit(p) ==
  {m \in Messages : m.origin = p /\ m.dest \in Proc /\ m.dest # p}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = Transmit(p)]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : timeout[p][q] < lastHeard[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p, msgs) ==
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.dest : m \in msgs}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF \E m \in msgs : m.origin = q THEN 0 ELSE lastHeard[p][q]]]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF \E m \in msgs : m.origin = q /\ q \in suspect[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] > 0 THEN clock[p] - 1 ELSE 0]

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ \E msgs \in SUBSET Messages : Receive(p, msgs)

Spec == Init /\ [][Next]_vars

====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, localClock, outbox

vars == <<suspect, timeout, lastHeard, localClock, outbox>>

\* Each process keeps a suspicion set of who it believes has crashed, an
\* adaptive timeout per peer, a counter of ticks since last hearing from each
\* peer, and a local clock governing when it sends or predicts.

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ localClock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ localClock[p] % SendPoint = 0
  /\ localClock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] ELSE (@ + 1)]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ localClock[p] % PredictPoint = 0
  /\ localClock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        suspect[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] ELSE (@ + 1)]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ localClock' = [localClock EXCEPT ![p] =
        IF @ + 1 > Max({SendPoint, PredictPoint} \cup {timeout[q][p] : q \in Proc})
        THEN 0 ELSE @ + 1]
  /\ suspect' = [suspect EXCEPT ![p] = {}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> 0]]
  /\ timeout' = [timeout EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspect[p] THEN @ + 1 ELSE @]]

Next ==
  \E p \in Proc:
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc: \A q \in Proc: lastHeard[p][q] \in Nat
  /\ \A p \in Proc: \A q \in Proc: timeout[p][q] \in Nat
  /\ \A p \in Proc: suspect[p] \subseteq Proc
  /\ \A p \in Proc: outbox[p] \subseteq Messages

====
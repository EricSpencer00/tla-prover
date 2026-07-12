---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\* Constants supplied by the configuration
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

CONSTANT MaxClock == SendPoint + PredictPoint + d0 + Len(Proc)

VARIABLES Suspicion, Timeout, LastHeard, Clock, Channel

vars == {Suspicion, Timeout, LastHeard, Clock, Channel}

\* Helper to construct an alive message
AliveMsg(p, q) == [sender |-> p, receiver |-> q, kind |-> "alive"]

\* Initial state
Init ==
  /\ Suspicion = [p \in Proc |-> {}]
  /\ Timeout  = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ Clock = 0
  /\ Channel = {}

\* Send alive messages
SendAlive(p) ==
  /\ p \in Proc
  /\ (Clock % SendPoint = 0)
  /\ (Clock % PredictPoint # 0)
  /\ LET msgs == {AliveMsg(p, q) : q \in Proc \ {p}} IN
  /\ Channel' = Channel \cup msgs
  /\ Suspicion' = Suspicion
  /\ Timeout' = Timeout
  /\ LastHeard' = [LastHeard EXCEPT ![p][q] = LastHeard[p][q] + 1 | q \in Proc \ {p}]
  /\ Clock' = (Clock + 1) % MaxClock

\* Update suspicion list
Predict(p) ==
  /\ p \in Proc
  /\ (Clock % PredictPoint = 0)
  /\ (Clock % SendPoint # 0)
  /\ LET newS == Suspicion[p] \ { q \in Proc : LastHeard[p][q] > Timeout[p][q] } IN
  /\ Suspicion' = [Suspicion EXCEPT ![p] = newS]
  /\ Timeout' = Timeout
  /\ LastHeard' = [LastHeard EXCEPT ![p][q] = LastHeard[p][q] + 1 | q \in Proc \ {p}]
  /\ Clock' = (Clock + 1) % MaxClock

\* Receive messages
Receive(p) ==
  /\ p \in Proc
  /\ LET M == { m \in Channel : m.receiver = p } IN
  /\ Channel' = Channel \ M
  /\ Suspicion' = [Suspicion EXCEPT ![p] = Suspicion[p] \ M]
  /\ Timeout' = [Timeout EXCEPT ![p][q] = IF q \in M THEN Timeout[p][q] + 1 ELSE Timeout[p][q] | q \in Proc]
  /\ LastHeard' = [LastHeard EXCEPT ![p][q] = IF q \in M THEN 0 ELSE LastHeard[p][q] | q \in Proc]
  /\ Clock' = Clock

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

\* Safety invariant (type correctness)
TypeOK ==
  /\ Suspicion \in [Proc -> SUBSET Proc]
  /\ Timeout  \in [Proc -> [Proc -> Nat]]
  /\ LastHeard \in [Proc -> [Proc -> Nat]]
  /\ Clock \in Nat
  /\ Channel \subseteq Messages

====
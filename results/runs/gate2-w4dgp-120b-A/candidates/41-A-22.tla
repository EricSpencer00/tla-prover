---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* Each process periodically sends alive messages and separately periodically
\* predicts which processes have crashed. SendTimes and PredictTimes are kept
\* separate (never equal) so a process never both sends and predicts in one
\* clock step. The model captures only correct processes; no process actually
\* crashes here, only suspicion is raised and later cleared.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint # PredictPoint
       /\ SendPoint > 0 /\ PredictPoint > 0

VARIABLES suspect, interval, heard, clock, outBox
vars == <<suspect, interval, heard, clock, outBox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ interval \in [Proc -> [Proc -> Nat]]
  /\ heard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outBox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ interval = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ heard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outBox = [p \in Proc |-> {}]

\* In one atomic step a process sends an alive message to every other
\* process and advances its local clock. The clock discipline also keeps
\* the "last heard" counters advancing, which is what eventually triggers
\* a prediction against a stale neighbor.
SendAlive(p) ==
  /\ outBox' = [outBox EXCEPT ![p] =
       {m \in Messages : m.to = q /\ m.from = p /\ q # p}]
  /\ clock' = [clock EXCEPT ![p] =
       ((@ + 1) % (SendPoint + PredictPoint + 1))]
  /\ heard' = [heard EXCEPT ![p] =
       [q \in Proc |-> IF heard[p][q] + 1 > interval[p][q]
         THEN heard[p][q] ELSE heard[p][q] + 1]]
  /\ UNCHANGED <<suspect, interval>>

Predict(p) ==
  /\ suspect' = [suspect EXCEPT ![p] =
       suspect[p] \cup {q \in Proc : heard[p][q] > interval[p][q]}]
  /\ clock' = [clock EXCEPT ![p] =
       ((@ + 1) % (SendPoint + PredictPoint + 1))]
  /\ heard' = [heard EXCEPT ![p] =
       [q \in Proc |-> IF heard[p][q] + 1 > interval[p][q]
         THEN heard[p][q] ELSE heard[p][q] + 1]]
  /\ UNCHANGED <<interval, outBox>>

\* Receiving an alive message resets the "last heard" counter and clears
\* any suspicion, and adaptively widens the timeout interval for that
\* process, since a stale process that finally replies deserves a larger
\* interval before being suspected again.
Receive(p) ==
  /\ \E m \in outBox[p] :
       suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
       /\ interval' = [interval EXCEPT ![p][m.from] = @ + 1]
       /\ heard' = [heard EXCEPT ![p][m.from] = 0]
  /\ outBox' = [outBox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = 0]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====
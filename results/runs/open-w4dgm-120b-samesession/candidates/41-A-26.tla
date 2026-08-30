---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,        \* the set of processes in the system
  d0,          \* default timeout interval for every process
  SendPoint,   \* clock interval at which a process sends alive messages
  PredictPoint,\* clock interval at which a process makes predictions
  Messages     \* the set of alive-message types a process can send

\* No local clock value is ever negative; the clock is reset whenever it
\* exceeds the send, predict, or any process's timeout interval.
MaxClock == SendPoint + PredictPoint + d0 + 1

VARIABLES
  suspicion,   \* suspicion[ p ] = subset of Proc that p currently suspects
  timeout,     \* timeout[ p ][ q ] = timeout interval p uses for q
  elapsed,     \* elapsed[ p ][ q ] = ticks since p last heard from q
  clock,       \* clock[ p ] = p's local clock value
  outbox       \* outbox[ p ] = alive messages p is sending this transition

vars == << suspicion, timeout, elapsed, clock, outbox >>

TypeOK ==
  /\ suspicion \in [ Proc -> SUBSET Proc ]
  /\ timeout \in [ Proc -> [ Proc -> Nat ] ]
  /\ elapsed \in [ Proc -> [ Proc -> Nat ] ]
  /\ clock \in [ Proc -> 0 .. MaxClock ]
  /\ outbox \in [ Proc -> SUBSET Messages ]

Init ==
  /\ suspicion = [ p \in Proc |-> {} ]
  /\ timeout = [ p \in Proc |-> [ q \in Proc |-> d0 ] ]
  /\ elapsed = [ p \in Proc |-> [ q \in Proc |-> 0 ] ]
  /\ clock = [ p \in Proc |-> 0 ]
  /\ outbox = [ p \in Proc |-> {} ]

\* Sending: a process at a send clock value creates a message for every other
\* process. Sending advances the clock and ages every non-timeout counter.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [ outbox EXCEPT ![p] = @ \cup Messages ]
  /\ clock' = [ clock EXCEPT ![p] = @ + 1 ]
  /\ elapsed' = [ elapsed EXCEPT ![p] =
        [ q \in Proc |-> IF elapsed[p][q] < timeout[p][q] THEN @ + 1 ELSE @ ] ]
  /\ UNCHANGED << suspicion, timeout >>

\* Predicting: a process at a predict clock value suspects any process whose
\* last-heard counter exceeds its timeout interval. Predicting also advances
\* the clock and ages every non-timeout counter.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [ suspicion EXCEPT ![p] = @ \cup
        { q \in Proc : elapsed[p][q] > timeout[p][q] } ]
  /\ clock' = [ clock EXCEPT ![p] = @ + 1 ]
  /\ elapsed' = [ elapsed EXCEPT ![p] =
        [ q \in Proc |-> IF elapsed[p][q] < timeout[p][q] THEN @ + 1 ELSE @ ] ]
  /\ UNCHANGED << timeout, outbox >>

\* Receiving: at all other clock values a process receives messages. Receiving
\* an alive message resets the sender's counter, removes it from suspicion,
\* and if it was a suspected sender the timeout interval is raised (adaptive).
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
        /\ suspicion' = [ suspicion EXCEPT ![p] =
              IF m \in suspicion[p] THEN @ \ { m } ELSE @ ]
        /\ elapsed' = [ elapsed EXCEPT ![p][m] = 0 ]
        /\ timeout' = [ timeout EXCEPT ![p][m] =
              IF m \in suspicion[p] THEN @ + 1 ELSE @ ]
        /\ outbox' = [ outbox EXCEPT ![p] = @ \ { m } ]
  /\ clock' = [ clock EXCEPT ![p] = @ + 1 ]

\* Reset: once the clock has passed every send, predict, and timeout
\* threshold, it is reset to zero so the clock domain stays finite.
ResetClock(p) ==
  /\ clock[p] > MaxClock
  /\ clock' = [ clock EXCEPT ![p] = 0 ]
  /\ UNCHANGED << suspicion, timeout, elapsed, outbox >>

Next ==
  /\ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

\* Every process must have strictly positive, non-nested send and predict
\* intervals so that alive messages and predictions are never emitted at
\* the same clock value; otherwise a process could be stuck in the other.
TimingSeparation ==
  /\ SendPoint \in Nat /\ SendPoint > 0
  /\ PredictPoint \in Nat /\ PredictPoint > 0
  /\ SendPoint % PredictPoint # 0
  /\ PredictPoint % SendPoint # 0

====
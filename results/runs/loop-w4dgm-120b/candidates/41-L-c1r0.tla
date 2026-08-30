---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,        \* set of processes in the system
  d0,          \* default timeout interval
  SendPoint,   \* clock values at which a process sends alive messages
  PredictPoint,\* clock values at which a process makes predictions
  Messages     \* set of alive messages (sender, receiver)

VARIABLES
  suspect,    \* suspect[p]: set of processes p suspects crashed
  timeout,    \* timeout[p]: [Proc -> Nat] adaptive timeout intervals
  lastHeard,  \* lastHeard[p]: [Proc -> Nat] ticks since p last heard from each other process
  clock,      \* clock[p]: local clock for process p
  outbox      \* outbox[p]: set of alive messages p intends to send

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

\* Process p sends an alive message to everyone, and ticks last-heard counters
Send(p) ==
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m[1] = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        [r \in Proc |->
           IF r = p \/ r = q THEN lastHeard[q][r]
           ELSE lastHeard[q][r] + 1]]
  /\ UNCHANGED <<suspect, timeout>>

\* Process p predicts based on timeout: it suspects any process not heard from
Predict(p) ==
  /\ suspect' = [suspect EXCEPT ![p] =
        { r \in Proc : r # p /\ lastHeard[p][r] > timeout[p][r] }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        [r \in Proc |->
           IF r = p \/ r = q THEN lastHeard[q][r]
           ELSE lastHeard[q][r] + 1]]
  /\ UNCHANGED <<timeout, outbox>>

\* Process p receives a message, clearing suspicion; an incoming message raises
\* the timeout counter for that sender (adaptive timeout)
Receive(p) ==
  /\ \E m \in outbox[p] : m[2] = p
  /\ suspect' = [q \in Proc |-> IF q = p THEN suspect[p] \ {m[1] : m \in outbox[p] /\ m[2] = p} ELSE suspect[q]]
  /\ timeout' = [q \in Proc |-> IF q = p /\ \E m \in outbox[p] : m[2] = p /\ m[1] = r THEN timeout[p][r] + 1 ELSE timeout[p][r]]
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m \in outbox[p] : m[2] = p}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > 3 THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED lastHeard

\* A process that is not sending and not predicting still ticks its clock and
\* its last-heard counters so the model never deadlocks
Tick(p) ==
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > 3 THEN 0 ELSE clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        [r \in Proc |->
           IF r = p \/ r = q THEN lastHeard[q][r]
           ELSE lastHeard[q][r] + 1]]
  /\ UNCHANGED <<suspect, timeout, outbox>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [r \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [r \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

Next ==
  \E p \in Proc :
    \/ Send(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ Tick(p)

Spec == Init /\ [][Next]_vars

====
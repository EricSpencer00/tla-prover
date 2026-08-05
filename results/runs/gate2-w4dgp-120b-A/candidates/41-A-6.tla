---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS
  Proc,       \* the set of processes in the system
  d0,         \* the default timeout interval for all processes
  SendPoint,  \* clock points at which a process sends alive messages
  PredictPoint,\* clock points at which a process makes a crash prediction
  Messages    \* the set of all possible alive messages

VARIABLES
  sus,        \* sus[p] = set of processes p currently suspects as crashed
  interval,   \* interval[p][q] = the adaptive timeout interval p uses for q
  clock,      \* clock[p] = the local clock value for process p
  pending,    \* pending[p] = the set of messages p wants to send this step
  lastHeard   \* lastHeard[p][q] = ticks since p last heard from q

vars == << sus, interval, clock, pending, lastHeard >>

\* An alive message addressed to q from p is in flight when p has put it in
\* its pending set and q has not yet processed it.
InFlight(p, q) ==
  \E m \in pending[p] : m.from = p /\ m.to = q

Init ==
  /\ sus = [p \in Proc |-> {}]
  /\ interval = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ clock = [p \in Proc |-> 0]
  /\ pending = [p \in Proc |-> {}]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]

\* A process sends alive messages to all other processes on a send clock tick.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ pending' = [pending EXCEPT ![p] = { m \in Messages : m.from = p }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |->
          IF lastHeard[p][q] < interval[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED << sus, interval >>

\* On a predict clock tick, processes add all processes they have timed out on to
\* their suspicion set.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ sus' = [sus EXCEPT ![p] =
        { q \in (sus[p] \cup { q \in Proc : lastHeard[p][q] >= interval[p][q] })
            \ { p } }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |->
          IF lastHeard[p][q] < interval[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED << interval, pending >>

\* A process processes whatever is in flight: it resets the last-heard counter
\* and drops the suspicion, and if the sender was suspected it bumps the
\* timeout interval (the adaptive step).
Receive(p) ==
  /\ \A q \in Proc : InFlight(q, p) => lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
  /\ \A q \in Proc : InFlight(q, p) => sus' = [sus EXCEPT ![p] = sus[p] \ { q }]
  /\ \A q \in Proc :
        InFlight(q, p) /\ q \in sus[p] => interval' = [interval EXCEPT ![p][q] = @ + 1]
  /\ \A p2 \in Proc : (~\E q \in Proc : InFlight(p2, q)) => interval' = interval
  /\ clock' = [p \in Proc |->
        IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ clock[p] > interval[p][p]
        THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc, q \in Proc : lastHeard[p][q] \in Nat /\ interval[p][q] \in Nat
  /\ \A p \in Proc : sus[p] \subseteq Proc
  /\ \A p \in Proc : pending[p] \subseteq Messages

====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

\* A process sends alive messages to everybody else every SendPoint ticks.
\* It makes failure predictions every PredictPoint ticks. The two intervals
\* must never be multiples of one another (see SendPoint < PredictPoint below),
\* which is what keeps alive sends and failure predictions apart. An
\* adaptation lets timeout intervals grow when a suspected process still
\* manages to send traffic.

VARIABLES
    sus, interval, lastHeard, clock, pending

vars == << sus, interval, lastHeard, clock, pending >>

SentBy(p) == {m \in pending : m.to = p}
ReceivedFrom(p) == {m \in pending : m.from = p}
Other(p) == Proc \ {p}

Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ interval = [p \in Proc |-> [q \in Other(p) |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Other(p) |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = {}

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = { [from |-> p, to |-> q] : q \in Other(p) } \cup pending
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Other(p) |-> IF lastHeard[p][q] < interval[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED << sus, interval >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ sus' = [sus EXCEPT ![p] = { q \in Other(p) : lastHeard[p][q] > interval[p][q] } \cup sus[p] ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Other(p) |-> IF lastHeard[p][q] < interval[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED << interval, pending >>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = pending \ SentBy(p)
    /\ sus' = [sus EXCEPT ![p] = sus[p] \ ReceivedFrom(p)]
    /\ interval' = [interval EXCEPT ![p] = [q \in Other(p) |-> IF \E m \in ReceivedFrom(p) : m.from = q THEN interval[p][q] + 1 ELSE interval[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Other(p) |-> IF \E m \in ReceivedFrom(p) : m.from = q THEN 0 ELSE lastHeard[p][q]]]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ interval \in [Proc -> [Proc -> Nat]]
    /\ sus \in [Proc -> SUBSET Proc]
    /\ pending \subseteq Messages

====
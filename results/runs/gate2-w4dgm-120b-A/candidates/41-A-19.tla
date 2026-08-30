---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Alive messages a process wants to send in the current transition.
Active == [to: Proc, from: Proc]

VARIABLES clock, suspect, timeout, lastHeard, pending

vars == <<clock, suspect, timeout, lastHeard, pending>>


TypeOK ==
    /\ clock \in [Proc -> 0 .. PredictPoint + SendPoint]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> SUBSET Proc]
    /\ lastHeard \in [Proc -> [Proc -> 0 .. Max(d0, PredictPoint)]]
    /\ pending \in [Proc -> SUBSET Active]

Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> {}]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
    /\ pending' = [pending EXCEPT ![p] = {a \in Active : a.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in timeout[p] THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

\* A process adds to its suspicion set every process it has not heard from within timeout.
Predict(p) ==
    /\ (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)
    /\ suspect' = [suspect EXCEPT ![p] =
                        @ \cup {q \in Proc : lastHeard[p][q] > Cardinality(timeout[p])}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in timeout[p] THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, pending>>

\* Receiving an alive message resets the counter and removes the sender from the suspicion set.
Receive(p, msgs) ==
    /\ msgs # {}
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ suspect' = [suspect EXCEPT ![p] =
                        @ \ {a.from : a \in msgs}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF \E a \in msgs : a.from = q THEN 0 ELSE lastHeard[p][q]]]
    /\ timeout' = [timeout EXCEPT ![p] =
                        @ \cup {a.from : a \in msgs \cap suspect[p]}]
    /\ pending' = [pending EXCEPT ![p] = {}]

Wrap(p) ==
    /\ clock[p] > PredictPoint + SendPoint
    /\ \A q \in Proc : lastHeard[p][q] <= Cardinality(timeout[p])
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, pending>>

Next ==
    \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Wrap(p)
    \/ \E p \in Proc, msgs \in SUBSET pending[p] : Receive(p, msgs)

Spec == Init /\ [][Next]_vars

====
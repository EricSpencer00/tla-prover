---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

VARIABLES
    suspects,
    timeout,
    lastHeard,
    clock,
    outbox

TypeInv ==
    /\ suspects \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspects = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* A process sends alive messages at every multiple of SendPoint, but only when
\* that tick is not also a multiple of PredictPoint.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dest = q}
                                                \cup (outbox[p] \ {m \in Messages : m.dest = p})]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in suspects[p] /\ lastHeard[p] < timeout[p]
                        THEN lastHeard[p] + 1 ELSE lastHeard[p]]
    /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspects' = [p \in Proc |->
                      suspects[p] \cup {q \in Proc : lastHeard[p] >= timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in suspects[p] /\ lastHeard[p] < timeout[p]
                        THEN lastHeard[p] + 1 ELSE lastHeard[p]]
    /\ UNCHANGED <<timeout, outbox>>

\* Receiving resets the last-heard counter and removes the sender from the
\* suspicion set. If the sender was previously suspected, the timeout interval
\* for that sender grows, modeling the adaptive timeout mechanism.
Receive(p) ==
    /\ outbox[p] # {}
    /\ suspects' = [p \in Proc |-> suspects[p] \ {m.dest : m \in outbox[p]}]
    /\ timeout' = [q \in Proc |-> IF \E m \in outbox[p] : m.dest = q /\ q \in suspects[p]
                                   THEN timeout[p] + 1 ELSE timeout[p]]
    /\ lastHeard' = [q \in Proc |-> IF \E m \in outbox[p] : m.dest = q THEN 0 ELSE lastHeard[p]]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [q \in Proc |-> IF q = p THEN 0 ELSE clock[q]]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

vars == <<suspects, timeout, lastHeard, clock, outbox>>

Spec == Init /\ [][Next]_vars

TypeOK == TypeInv

====
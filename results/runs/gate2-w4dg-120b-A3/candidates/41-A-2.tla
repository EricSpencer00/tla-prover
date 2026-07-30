---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

\* The action interval constants are constrained to never coincide (SendPoint is
\* not a multiple of PredictPoint, and vice versa) -- this is what keeps Send
\* and Predict from ever being enabled at the same clock value.  The module
\* does not itself enforce the constraint; it is assumed to hold in every
\* reachable state, and the controlling deployment must pick values accordingly.
\* All timeout intervals start at a fixed value d0 and only grow from there.

VARIABLES suspicion, timeout, lastHeard, clock, transmit

vars == <<suspicion, timeout, lastHeard, clock, transmit>>

Message == [from : Proc, to : Proc, tag : {"alive"}]

TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ transmit \in [Proc -> SUBSET Messages]

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ transmit = [p \in Proc |-> {}]

Tick(p) ==
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, transmit>>

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ transmit' = [transmit EXCEPT ![p] = {
            [from |-> p, to |-> q, tag |-> "alive"] : q \in Proc, q # p}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p
                          THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ Tick(p)

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
           {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p
                          THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ Tick(p)

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E msgs \in SUBSET Messages :
        /\ \A m \in msgs : m.to = p
        /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF \E m \in msgs : m.from = q
                                  THEN 0 ELSE lastHeard[p][q]]]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q \in Proc : \E m \in msgs : m.from = q}]
        /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF \E m \in msgs : m.from = q /\ q \in suspicion[p]
                            THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
        /\ transmit' = [transmit EXCEPT ![p] = transmit[p] \ msgs]
    /\ Tick(p)

ResetClocks(p) ==
    /\ \E thr \in Nat :
        /\ clock[p] > thr
        /\ thr >= SendPoint
        /\ thr >= PredictPoint
        /\ \A q \in Proc : thr >= timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> 0]]
    /\ UNCHANGED <<suspicion, timeout, transmit>>

Next ==
    \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ ResetClocks(p)

Spec == Init /\ [][Next]_vars

====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

\* Sender/Receiver is a process; Target is the process a message is about;
\* the empty Target marks a clock tick that sends no messages.
Message == [Sender : Proc, Target : Proc \cup {"empty"}]

VARIABLES
    suspicion,
    timeout,
    lastHeard,
    clock,
    outgoing

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

\* Send and Predict are driven by the local clock and never fire together,
\* because SendPoint and PredictPoint do not coincide.
Bump(p) == IF clock[p] = 0 THEN 1 ELSE clock[p]

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = { [ Sender |-> p, Target |-> q ] : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = Bump(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] ]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] ]]
    /\ clock' = [clock EXCEPT ![p] = Bump(p)]
    /\ UNCHANGED <<timeout, outgoing>>

\* Receiving an alive message resets the counter and clears the suspicion;
\* a suspected process that does send raises its timeout (adaptive timeout).
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF \E m \in outgoing[p] : m.Target = q
                            THEN 0 ELSE lastHeard[p][q] ]]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { q \in Proc : \E m \in outgoing[p] : m.Target = q } ]
    /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
                            IF q \in suspicion[p] /\ \E m \in outgoing[p] : m.Target = q
                            THEN timeout[p][q] + 1 ELSE timeout[p][q] ]]
    /\ clock' = [clock EXCEPT ![p] = IF Bump(p) > 3 THEN 0 ELSE Bump(p)]
    /\ UNCHANGED <<outgoing>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Message]

====
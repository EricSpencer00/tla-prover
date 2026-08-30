---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outgoing

\* A process p creates one Message for each distinct destination; p never creates
\* two messages to the same destination in one sending operation.
Message == {m \in Messages : m.sender = p /\ m.dest # p}

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outgoing \in [Proc -> SUBSET Message]
    /\ clock \in [Proc -> 1 .. (SendPoint + PredictPoint + d0)]

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* Alive messages are broadcast to every other process at once, synchronized
\* on a local clock that never aligns with the prediction clock.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = Message]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF q \in Message THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<suspicion, timeout>>

\* A process suspects q once the time since last hearing from q exceeds the
\* timeout currently in force for q.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup
                        {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF q \in Message THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<timeout, outgoing>>

\* Receiving an alive message from a suspected process drops the suspicion and,
\* if it was a late message, expands the timeout for that process.
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outgoing[p]:
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.dest] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {m.dest}]
        /\ timeout' = [timeout EXCEPT ![p][m.dest] =
                        IF m.dest \in suspicion[p] THEN @ + 1 ELSE @]
        /\ outgoing' = [outgoing EXCEPT ![p] = @ \ {m}]
    /\ clock' = [clock EXCEPT ![p] = IF @ = SendPoint + PredictPoint + d0
                                            THEN 0 ELSE @ + 1]

Next ==
    \/ \E p \in Proc: SendAlive(p)
    \/ \E p \in Proc: Predict(p)
    \/ \E p \in Proc: Receive(p)

Spec == Init /\ [][Next]_vars

====
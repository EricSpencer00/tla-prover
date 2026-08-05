---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* An eventually perfect failure detector: a correct process only temporarily
\* suspects a slow or absent process, then never again once it receives a
\* message from it. Time evolves in local clocks, and the send and predict
\* clocks are deliberately kept out of phase so the two actions never
\* happen in the same step (this models the separate periodic actions in
\* the Chandra/Toueg framework).

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, localClock, outgoingMsgs

vars == <<suspicion, timeout, lastHeard, localClock, outgoingMsgs>>

NoOne == {}

\* A process p is considered recently heard from if it has not yet timed out
\* on any other process; this gate keeps the model finite by bounding the
\* growth of the lastHeard counters (they only tick while p is still
\* waiting for something it has not timed out on).
IsNotTimedOut(p) == \A q \in Proc : lastHeard[p][q] < timeout[p][q]

Init ==
    /\ suspicion = [p \in Proc |-> NoOne]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ localClock = [p \in Proc |-> 0]
    /\ outgoingMsgs = [p \in Proc |-> {}]

\* Send an alive message to every other process; fire only at a SendPoint
\* clock value (never at a PredictPoint value, thanks to the constants).
SendAlive(p) ==
    /\ localClock[p] % SendPoint = 0
    /\ localClock[p] % PredictPoint # 0
    /\ outgoingMsgs' = [outgoingMsgs EXCEPT ![p] = {m \in Messages : m.to \in Proc}]
    /\ localClock' = [localClock EXCEPT ![p] = localClock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspicion, timeout>>

\* Periodically re-evaluate who is suspected, based on the adaptive timeout.
Predict(p) ==
    /\ localClock[p] % PredictPoint = 0
    /\ localClock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q \in Proc : lastHeard[p][q] >= timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ localClock' = [localClock EXCEPT ![p] = localClock[p] + 1]
    /\ UNCHANGED <<timeout, outgoingMsgs>>

\* Receive incoming messages; a message from a formerly suspected process
\* clears that suspicion and adaptively increases the timeout for that
\* process's path.
Receive(p) ==
    /\ ~ (localClock[p] % SendPoint = 0 /\ localClock[p] % PredictPoint # 0)
    /\ ~ (localClock[p] % PredictPoint = 0 /\ localClock[p] % SendPoint # 0)
    /\ \E m \in outgoingMsgs[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.to] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {m.to}]
        /\ timeout' = [timeout EXCEPT ![p][m.to] = timeout[p][m.to] + 1]
    /\ localClock' = [localClock EXCEPT ![p] = IF IsNotTimedOut(p) THEN localClock[p] + 1 ELSE 0]
    /\ outgoingMsgs' = [outgoingMsgs EXCEPT ![p] = {}]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : outgoingMsgs[p] \subseteq Messages

====
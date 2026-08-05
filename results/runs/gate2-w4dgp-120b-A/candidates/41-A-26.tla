---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
    suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* Clock-driven: a process with its own local clock sends alive messages at every
\* multiple of SendPoint and evaluates its suspicion list at every multiple of
\* PredictPoint (these two points never coincide). LastHeard counts ticks since a
\* message was last received from each other process.

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* A process sends alive messages addressed to every other process.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dest = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<suspect, timeout>>

\* Based on the adaptive timeout, a process suspects anyone it has not heard from.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc :
                        IF q = p THEN @ ELSE
                        IF lastHeard[p][q] > timeout[p][q] THEN @ \cup {q} ELSE @}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> @ + 1]]
    /\ UNCHANGED <<timeout, outbox>>

\* Receiving resets the last-heard counter; a message from a suspected process
\* expands that process's timeout, the adaptive mechanism.
Receive(p) ==
    /\ clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
    /\ \E msg \in outbox[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![p][msg.dest] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = IF msg.dest \in suspect[p] THEN @ \ {msg.dest} ELSE @]
        /\ timeout' = [timeout EXCEPT ![p][msg.dest] =
                         IF msg.dest \in suspect[p] THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = @ \ {msg}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* The local clock is always bounded: it resets when it would exceed any relevant
\* threshold, keeping the state space finite.
ResetClock(p) ==
    /\ clock[p] > SendPoint /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

\* A process performs exactly one of the above actions per clock step.
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat] /\ suspect[p] \subseteq Proc
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ outbox \subseteq [dest : Proc]

====
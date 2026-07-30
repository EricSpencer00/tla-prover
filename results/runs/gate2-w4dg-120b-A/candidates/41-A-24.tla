---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, outbox

vars == <<clock, suspect, timeout, lastHeard, outbox>>

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : outbox[p] \subseteq Messages
    /\ \A p \in Proc : clock[p] \in Nat

Init ==
    /\ \A p \in Proc :
         /\ suspect[p] = {}
         /\ timeout[p] = [q \in Proc |-> d0]
         /\ lastHeard[p] = [q \in Proc |-> 0]
         /\ clock[p] = 0
         /\ outbox[p] = {}

\* A process sends alive messages to every other process on a send tick.
SendAlive(p) ==
    /\ p \in Proc
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = q /\ m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ UNCHANGED suspect
    /\ UNCHANGED timeout

\* A process makes predictions about who has crashed on a predict tick.
Predict(p) ==
    /\ p \in Proc
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED timeout
    /\ UNCHANGED outbox

\* A process receives messages and reacts to them.
Receive(p) ==
    /\ p \in Proc
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outbox[p] :
         /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
         /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
         /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN timeout[p][m.from] + 1 ELSE timeout[p][m.from]]
         /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ \A q \in Proc : clock[p] + 1 > timeout[p][q] THEN 0 ELSE clock[p] + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

\* Bounded clocks: once the clock reaches every relevant threshold it resets to zero,
\* so the reachable state space stays finite even though the actions are otherwise open-ended.
ClockBound ==
    \A p \in Proc :
        (clock[p] >= SendPoint /\ clock[p] >= PredictPoint /\ \A q \in Proc : clock[p] >= timeout[p][q])
            => clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

SpecWithBound == Spec /\ [][ClockBound]_vars

\* The complete set of invariants the reference configuration expects.
INVARIANT SpecWithBound

====
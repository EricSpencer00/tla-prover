---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \subseteq [proc : Proc, about : Proc]
    /\ outbox \subseteq Messages
    /\ clock \in [Proc -> Nat]

\* The suspicion set is what survives; lastHeard is a helper that is reset
\* whenever an alive message is received.
Init ==
    /\ suspect = {}
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = {}

\* Send: the local clock reaches a send point but not a predict point,
\* and the process dispatches an alive message to every other process.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = outbox \cup {[proc |-> p, about |-> q] : q \in Proc, q # p}
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predict: the local clock reaches a predict point but not a send point,
\* and the process adds to its suspicion set anyone it has not heard from
\* within that process's current timeout interval.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = suspect \cup {[proc |-> p, about |-> q] : q \in Proc, q # p, lastHeard[p][q] > timeout[p][q]}
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outbox : m.about = p
    /\ LET S == {m \in outbox : m.about = p} IN
        /\ suspect' = suspect \ {[proc |-> m.proc, about |-> p] : m \in S}
        /\ timeout' = [timeout EXCEPT ![p] =
                         [q \in Proc |-> IF \E m \in S : m.proc = q THEN @[q] + 1 ELSE @[q]]]
        /\ outbox' = outbox \ S
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF \E m \in outbox : m.about = p /\ m.proc = q THEN 0 ELSE @[q]]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* A bounded local clock with a bounded timeout interval keeps the reachable
\* state space finite; the reset engages when all thresholds are passed.
Tick(p) ==
    /\ clock[p] > 0
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] >= timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ Tick(p)

Spec ==
    /\ Init
    /\ [][Next]_vars

====
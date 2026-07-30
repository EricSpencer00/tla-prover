---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

\* The description calls for non-coincident send and predict ticks: the
\* send clock must be at a multiple of SendPoint but never at a multiple
\* of PredictPoint, and vice versa.
NoCoincidence == SendPoint # PredictPoint

VARIABLES
    suspect,
    timeout,
    lastHeard,
    clock,
    outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \notin suspect[p] /\ lastHeard[q] < timeout[q] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \notin suspect[p] /\ lastHeard[q] < timeout[q] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ LET deliver == {m \in outbox[p] : m.to = p} IN
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from : m \in deliver}]
       /\ timeout' = [q \in Proc |-> IF q \in {m.from : m \in deliver} /\ q \in suspect[p] THEN timeout[q] + 1 ELSE @]
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > timeout[p] THEN 0 ELSE @ + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ lastHeard' = [q \in Proc |-> IF q \notin suspect[p] /\ lastHeard[q] < timeout[q] THEN @ + 1 ELSE @]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

\* The spec's full safety contract is this type invariant; the description
\* has no additional functional property to assert.
INVARIANT TypeOK
====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A process may be slow but never fails; it keeps sending alive messages and
\* re-predicts, so every process eventually learns the truth about every other.
\* Suspicions are therefore only temporary and always eventually cleared.

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Message == [src : Proc, dst : Proc]
msgs == {m \in Messages : m.src # m.dst}

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> 0..d0]]
    /\ timeout \in [Proc -> [Proc -> 1..d0]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Message]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Time advances only by catching up on a timed-out process, so the no-stale
\* assignment below is reachable even when every process can be slow.
CatchUp(p, q) == IF clock[p] < timeout[p][q] THEN clock[p] + 1 ELSE clock[p]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [src |-> p, dst |-> q] : q \in Proc } \ msgs]
    /\ clock' = [clock EXCEPT ![p] = CatchUp(p, p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0 ELSE IF lastHeard[p][q] >= timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = { q \in Proc : lastHeard[p][q] > timeout[p][q] } \ msgs]
    /\ clock' = [clock EXCEPT ![p] = CatchUp(p, p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0 ELSE IF lastHeard[p][q] >= timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E arr \in SUBSET msgs :
         /\ \A m \in arr : m.dst = p /\ m \in outbox[m.src]
         /\ outbox' = [q \in Proc |-> outbox[q] \ {m \in outbox[q] : m.dst = p}]
         /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in {m.src : m \in arr} THEN 0 ELSE lastHeard[p][q]]]
         /\ suspect' = [suspect EXCEPT ![p] = { q \in suspect[p] : q \notin {m.src : m \in arr} } \ msgs]
         /\ timeout' = [q \in Proc |-> IF q \in {m.src : m \in arr} THEN IF timeout[p][q] < d0 THEN timeout[p][q] + 1 ELSE timeout[p][q] ELSE timeout[p][q]]
    /\ clock' = [clock EXCEPT ![p] = CatchUp(p, p)]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Proc : SendAlive(p))
    /\ WF_vars(\E p \in Proc : Predict(p))
    /\ WF_vars(\E p \in Proc : Receive(p))

SpecOK == Spec /\ TypeOK

====
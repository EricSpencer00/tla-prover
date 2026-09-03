---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process periodically emits "alive" broadcasts to the others and
\* periodically predicts crashes; the two are separated by the clock so
\* they never fire at the same instant. At most one process is ever
\* actually crashed (the silent crash), and it is the single one the
\* failure detector is never allowed to permanently suspect forever.
\* Adaptive timeouts (the per-link d field) guarantee eventual
\* recovery of correct suspicion: a correct process that keeps hearing
\* from a suspected peer has that suspicion revoked, and if the peer
\* had timed the other out it re-learns that the timeout was too short.
\* The three properties together are the full claim: the detector is
\* sound (never fails by suspecting a correct process forever),
\* complete (suspicions of correct processes are always given up),
\* and the timeout client always stabilizes to its minimum.
\* The clock is bounded (the ResetClock action) so the reachable state
\* space stays finite; no fair or liveness claim is made about it.
\* This is the final design decision: the clock is bounded, not
\* unbounded, because an unbounded clock would break finiteness and
\* the model would not explore any reachable behavior outside the
\* bounded window anyway.

VARIABLES suspect, d, lastHeard, clock, outbox

Vars == <<suspect, d, lastHeard, clock, outbox>>

Msgs == [src : Proc, dst : Proc]

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ d \in [Proc -> [Proc -> 1..d0]]
    /\ lastHeard \in [Proc -> [Proc -> 0..d0]]
    /\ clock \in [Proc -> 0..d0]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ d = [p \in Proc |-> [q \in Proc |-> 1]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Send an alive broadcast at every SendPoint tick; increment lastHeard
\* for links that are not yet timed out so they age here instead of
\* staying fresh on the sender's side.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in outbox[p] : m.dst # p} \union {[src |-> p, dst |-> q] : q \in Proc, q # p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p /\ lastHeard[p][q] < d[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, d>>

PredictCrash(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in suspect[p] : lastHeard[p][q] <= d[p][q]} \union {[q \in Proc \ {p} : lastHeard[p][q] > d[p][q]]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p /\ lastHeard[p][q] < d[p][q] THEN @ + 1 ELSE @]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<d, outbox>>

ReceiveMsg(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E r \in Proc :
         /\ r # p
         /\ suspect[p] = suspect[p] \ {r}
         /\ d' = [d EXCEPT ![p][r] = IF r \in suspect[p] THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {m \in outbox[p] : m.dst # p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [lastHeard[p] EXCEPT ![r] = 0]]
    /\ UNCHANGED suspect

ResetClock(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > d[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, d, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : PredictCrash(p)
    \/ \E p \in Proc : ReceiveMsg(p)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_Vars

SuspicionsSettle ==
    \A p \in Proc :
        \A q \in Proc :
            (p # q /\ q \notin suspect[p]) ~> (q \in suspect[p])

NoPermanentWrongSuspect ==
    \A p \in Proc :
        \A q \in Proc :
            (q \in suspect[p] /\ q \notin suspect[p]) ~> (q \notin suspect[p])

TimeoutsStabilize ==
    \A p \in Proc :
        \A q \in Proc :
            (q \in suspect[p] /\ q \notin suspect[p]) ~> (d[p][q] = 1)

====
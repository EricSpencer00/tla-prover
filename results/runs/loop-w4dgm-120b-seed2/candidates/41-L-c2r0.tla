---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process holds its own clock; send and predict actions are gated on it
\* so that they never fire at the same instant (the intervals are kept coprime).
\* LastHeard[p][q] counts ticks since p last heard from q; TimeOut[p][q] is p's
\* adaptive timeout interval for q: q is suspected once the count exceeds it.

VARIABLES Suspected, TimeOut, LastHeard, Clock, Outgoing

TypeOK ==
    /\ Suspected \in [Proc -> SUBSET Proc]
    /\ TimeOut \in [Proc -> [Proc -> Nat]]
    /\ LastHeard \in [Proc -> [Proc -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Outgoing \in [Proc -> SUBSET Messages]

\* When a process p times out waiting for q it adds q to its suspicion set, and
\* when a suspected q sends a message p receives, p raises q's timeout interval
\* rather than dropping the suspicion outright -- this is the adaptive part.
Init ==
    /\ Suspected = [p \in Proc |-> {}]
    /\ TimeOut = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock = [p \in Proc |-> 0]
    /\ Outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint = 1
    /\ Outgoing' = [Outgoing EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ Clock' = [Clock EXCEPT ![p] = @ + 1]
    /\ LastHeard' = [LastHeard EXCEPT ![p] =
            [q \in Proc |-> IF q \in Suspected[p] /\ LastHeard[p][q] >= TimeOut[p][q]
                           THEN LastHeard[p][q] ELSE LastHeard[p][q] + 1]]
    /\ UNCHANGED <<Suspected, TimeOut>>

Predict(p) ==
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint = 1
    /\ Suspected' = [Suspected EXCEPT ![p] = {q \in Proc :
                    IF q \in Suspected[p] \/ LastHeard[p][q] > TimeOut[p][q]
                    THEN @ ELSE @ \cup {q} }]
    /\ Clock' = [Clock EXCEPT ![p] = @ + 1]
    /\ LastHeard' = [LastHeard EXCEPT ![p] =
            [q \in Proc |-> IF q \in Suspected[p] /\ LastHeard[p][q] >= TimeOut[p][q]
                           THEN LastHeard[p][q] ELSE LastHeard[p][q] + 1]]
    /\ UNCHANGED <<TimeOut, Outgoing>>

Receive(p) ==
    /\ \E r \in [From : Proc, To : Proc] : r \in Outgoing[p]
    /\ Suspected' = [Suspected EXCEPT ![p] =
            @ \ {r.from : r \in {r \in Outgoing[p] : r.from # p /\ r.to = p /\ r.from \in Suspected[p]}}
    /\ TimeOut' = [TimeOut EXCEPT ![p] =
            [q \in Proc |-> IF \E r \in Outgoing[p] :
                            /\ r.from = q /\ r.to = p /\ q \in Suspected[p] /\ r \in Outgoing[p]
                          THEN @ + 1 ELSE @]]
    /\ LastHeard' = [LastHeard EXCEPT ![p] =
            [q \in Proc |-> IF \E r \in Outgoing[p] : r.from = q /\ r.to = p
                           THEN 0 ELSE LastHeard[p][q]]]
    /\ Outgoing' = [Outgoing EXCEPT ![p] = {}]
    /\ Clock' = [Clock EXCEPT ![p] = IF Clock[p] + 1 > SendPoint
                                          THEN 0 ELSE Clock[p] + 1]

\* The clock is bounded: once it has passed every send tick, predict tick,
\* and any active timeout interval, it is reset, so each process's clock
\* domain stays finite even though the protocol runs forever.
ResetClock(p) ==
    /\ Clock[p] > SendPoint
    /\ \A q \in Proc : Clock[p] > TimeOut[p][q]
    /\ \A q \in {p} \cup Suspected[p] : Clock[p] > PredictPoint
    /\ Clock' = [Clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<Suspected, TimeOut, LastHeard, Outgoing>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_<<Suspected, TimeOut, LastHeard, Clock, Outgoing>>

====
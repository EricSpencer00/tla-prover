---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process sends alive messages (at SendPoint ticks) and, separately,
\* makes crash-suspicions (at PredictPoint ticks).  d0 is the default timeout;
\* the adaptation happens when a suspected process proves us wrong by sending.
\* The clock is reset once it has passed every operational and timeout bound.
VARIABLES suspected, timeout, lastHeard, clock, pending

vars == <<suspected, timeout, lastHeard, clock, pending>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ pending \in [Proc -> SUBSET Messages]
    /\ clock \in [Proc -> Nat]

Init ==
    /\ suspected = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

Dead(p, q) == p # q /\ q \notin suspected[p]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m[1] = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF q \in suspected[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspected, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q \in Proc : Dead(p, q) /\ lastHeard[p][q] >= timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF q \in suspected[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
    /\ (clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0)
    /\ \E m \in pending[p] :
         LET q == m[1] IN
         /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
         /\ lastHeard' = [lastHeard EXCEPT ![p] = [lastHeard[p] EXCEPT ![q] = 0]]
         /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ {q}]
         /\ timeout' = [timeout EXCEPT ![p] = [timeout[p] EXCEPT ![q] = IF q \in suspected[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
    /\ pending' = [pending EXCEPT ![p] = pending[p] \ {m \in pending[p] : m[1] = p}]

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

\* Bounded capacity: no process's timeout ever grows past the next predict window.
TimeoutsStayBounded == \A p \in Proc : \A q \in Proc : timeout[p][q] <= PredictPoint

====
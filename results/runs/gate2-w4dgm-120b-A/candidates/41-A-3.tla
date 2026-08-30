---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, notHeard, clock, outbox

vars == <<suspect, timeout, notHeard, clock, outbox>>

NoReport == [from |-> "x", to |-> "x"]

\* true iff no process's clock-ready window is currently firing.
NoActionPending ==
    \A q \in Proc :
        ~((clock[q] % SendPoint = 0) /\ (clock[q] % PredictPoint # 0))
        /\ ~((clock[q] % PredictPoint = 0) /\ (clock[q] % SendPoint # 0))

TypeOK ==
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : notHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : clock[p] \in Nat
    /\ outbox \subseteq Messages

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ notHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = {}

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = {m \in outbox : m.from # p} \cup {[from |-> p, to |-> q] : q \in Proc \ {p}}
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0
                                                            ELSE IF @[q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p]
        \cup {q \in Proc : q # p /\ notHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0
                                                            ELSE IF @[q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p, m) ==
    /\ m \in outbox
    /\ m.to = p
    /\ outbox' = outbox \ {m}
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
    /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |-> IF q = m.from THEN 0 ELSE @]]
    /\ timeout' = [timeout EXCEPT ![p] = [timeout[p] EXCEPT ![m.from] =
                        IF m.from \in suspect[p] THEN @ + 1 ELSE @]]
    /\ UNCHANGED clock

ResetClock(p) ==
    /\ clock[p] > SendPoint * PredictPoint
    /\ \A q \in Proc :
         clock[p] > timeout[p][q] /\ clock[p] > SendPoint /\ clock[p] > PredictPoint
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, notHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc, m \in Messages : Receive(p, m)
    \/ \E p \in Proc : ResetClock(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ SF_vars(\E m \in Messages : Receive(1, m))
    /\ SF_vars(\E m \in Messages : Receive(2, m))
    /\ WF_vars(\E p \in Proc : SendAlive(p))
    /\ WF_vars(\E p \in Proc : Predict(p))
    /\ SF_vars(\E p \in Proc : ResetClock(p))
    /\ NoActionPending

====
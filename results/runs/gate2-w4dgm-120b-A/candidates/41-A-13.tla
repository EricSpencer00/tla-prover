---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A process's record: its suspicion set, per-neighbor timeout intervals,
\* a per-neighbor counter since last heard, a local clock, and its batch.
VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

Bump(c, m) == IF c < m THEN c + 1 ELSE c

\* Send an alive message to every other process; advance lastHeard for
\* neighbors that still lie within their timeout interval.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] =
                        {[src |-> p, dst |-> q] : q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = Bump(@, SendPoint + PredictPoint)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc \ {p} |-> IF lastHeard[q] < timeout[q]
                                                THEN lastHeard[q] + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predict which processes have crashed, based on adaptive timeouts.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                        {q \in Proc \ {p} : lastHeard[q] > timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = Bump(@, SendPoint + PredictPoint)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc \ {p} |-> IF lastHeard[q] < timeout[q]
                                                THEN lastHeard[q] + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outgoing>>

\* Receive whatever messages are pending for this process.
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E pkt \in outgoing[p] :
         /\ pkt.dst = p
         /\ lastHeard' = [lastHeard EXCEPT ![pkt.src] = 0]
         /\ suspect' = [suspect EXCEPT ![p] = @ \ {pkt.src}]
         /\ timeout' = [timeout EXCEPT ![pkt.src] =
                            IF pkt.src \in suspect[p] THEN @ + 1 ELSE @]
    /\ outgoing' = [outgoing EXCEPT ![p] = @ \ {pkt}]
    /\ clock' = [clock EXCEPT ![p] = Bump(@, SendPoint + PredictPoint)]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec = Init /\ [][Next]_vars

\* No process's last-heard counter may exceed its timeout interval.
NoStaleSuspicion == \A p \in Proc : suspect[p] \subseteq {q \in Proc : lastHeard[q] > timeout[q]}
====
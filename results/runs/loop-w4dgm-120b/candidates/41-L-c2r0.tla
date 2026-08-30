---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Adapted from the eventually perfect failure detector of Chandra and Toueg (1996):
\* processes send alive messages and predict crashes, never doing both at once.
\* The clock domain is bounded: when everything has rolled past the send and
\* predict points and all adaptive timeouts, the local clock resets.

ASSUME SendPoint \in Nat /\ SendPoint > 0
ASSUME PredictPoint \in Nat /\ PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0
ASSUME PredictPoint % SendPoint # 0

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

SendAlive ==
    /\ \E p \in Proc :
         /\ clock[p] % SendPoint = 0
         /\ clock[p] % PredictPoint # 0
         /\ outgoing' = [outgoing EXCEPT ![p] =
                 {m \in Messages : m.sender = p /\ m.verb = "alive"}]
         /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
         /\ lastHeard' = [lastHeard EXCEPT ![p] =
                 [q \in Proc |-> IF clock[p] + 1 <= timeout[p][q]
                               THEN lastHeard[p][q]
                               ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

Predict ==
    /\ \E p \in Proc :
         /\ clock[p] % PredictPoint = 0
         /\ clock[p] % SendPoint # 0
         /\ suspect' = [suspect EXCEPT ![p] =
                 @ \cup {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
         /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
         /\ lastHeard' = [lastHeard EXCEPT ![p] =
                 [q \in Proc |-> IF clock[p] + 1 <= timeout[p][q]
                               THEN lastHeard[p][q]
                               ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outgoing>>

Receive ==
    /\ \E p \in Proc :
         /\ \E S \in SUBSET {m \in Messages : m.recipient = p} :
              /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.sender : m \in S}]
              /\ timeout' = [timeout EXCEPT ![p] =
                   [q \in Proc |-> IF \E m \in S : m.sender = q
                                 THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
              /\ lastHeard' = [lastHeard EXCEPT ![p] =
                   [q \in Proc |-> IF \E m \in S : m.sender = q
                                 THEN 0 ELSE lastHeard[p][q]]]
         /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= d0
                                         THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED outgoing

Next == SendAlive \/ Predict \/ Receive

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendAlive)
    /\ WF_vars(Predict)
    /\ WF_vars(Receive)

\* Bounded clock: everything has rolled past its send/predict point and all
\* adaptive timeouts, so the local clock resets -- keeps the clock domain finite.
ClockBound == \A p \in Proc : clock[p] <= d0

====
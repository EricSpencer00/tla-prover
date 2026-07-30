---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* Process-local clock, per-process suspicion list, per-process adaptive
\* timeout intervals, and per-process last-heard counters are all
\* retained across steps -- they are never reset wholesale, only
\* incremented or locally updated, which is what keeps every step
\* monotone. The safety properties below are therefore just
\* structural.
\* The clock-interval arithmetic has to be safe even at the top of
\* the domain: sending or predicting at the top value would move
\* a counter out of range, so sending/predicting is only enabled
\* strictly below the top of the domain (rather than enabled at
\* the top and clamped back to the top on the same step).

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages
NONE == "none"

VARIABLES suspicion, timeout, lastHeard, clock, outbound

vars == <<suspicion, timeout, lastHeard, clock, outbound>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outbound \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbound = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ clock[p] < d0 + SendPoint
  /\ outbound' = [outbound EXCEPT ![p] = {m \in Messages : m.here = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF clock[p] + 1 > timeout[q] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ clock[p] < d0 + PredictPoint
  /\ suspicion' = [suspicion EXCEPT ![p] =
        @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF clock[p] + 1 > timeout[q] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<timeout, outbound>>

Receive(p) ==
  /\ clock[p] < d0 + SendPoint
  /\ clock[p] < d0 + PredictPoint
  /\ \A q \in Proc : clock[p] < d0 + timeout[q]
  /\ \/ \E m \in outbound[p] :
        /\ m.here # p
        /\ m.here \in Proc
        /\ lastHeard' = [lastHeard EXCEPT ![m.here] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {m.here}]
        /\ timeout' = [timeout EXCEPT ![m.here] = IF m.here \in @ THEN @ + 1 ELSE @]
        /\ outbound' = [outbound EXCEPT ![p] = @ \ {m}]
     \/ \E q \in Proc :
        /\ m.here = p
        /\ m.there = q
        /\ m \in outbound[q]
        /\ outbound' = [outbound EXCEPT ![q] = @ \ {m}]
        /\ UNCHANGED <<suspicion, timeout, lastHeard>>
  /\ clock' = [clock EXCEPT ![p] = IF @ = d0 + SendPoint
                                        \/ @ = d0 + PredictPoint
                                        \/ Sigma_{q \in Proc} timeout[q]
                                    THEN 0 ELSE @ + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
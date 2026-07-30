---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, localClock, pending

vars == <<suspect, timeout, lastHeard, localClock, pending>>

TypeOK ==
    /\ suspect \subseteq [process : Proc, target : Proc, kind : {"suspect"}]
    /\ timeout \in [process : Proc, target : Proc, kind : {"period"} |-> Nat]
    /\ lastHeard \in [process : Proc, target : Proc, kind : {"counter"} |-> Nat]
    /\ localClock \in [process : Proc, kind : {"now"} |-> Nat]

Init ==
    /\ suspect = {}
    /\ timeout = [p \in [process : Proc, target : Proc, kind : {"period"}] |-> d0]
    /\ lastHeard = [p \in [process : Proc, target : Proc, kind : {"counter"}] |-> 0]
    /\ localClock = [p \in [process : Proc, kind : {"now"}] |-> 0]
    /\ pending = {}

SendAlive(p) ==
    /\ localClock[p] % SendPoint = 0
    /\ localClock[p] % PredictPoint # 0
    /\ pending' = {m \in Messages : m.process = p}
    /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in DOMAIN lastHeard |-> IF q.process = p /\ q.target # p /\ lastHeard[q] < timeout[p, q.target] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ localClock[p] % PredictPoint = 0
    /\ localClock[p] % SendPoint # 0
    /\ suspect' = {q \in suspect} \cup
                   {[\process |-> p, target |-> tt, kind |-> "suspect"] :
                        tt \in Proc : tt # p /\ lastHeard[p, tt] > timeout[p, tt]}
    /\ lastHeard' = [q \in DOMAIN lastHeard |-> IF q.process = p /\ lastHeard[q] < timeout[p, q.target] THEN @ + 1 ELSE @]
    /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
    /\ pending' = {}
    /\ lastHeard' = [q \in DOMAIN lastHeard |-> IF q.process = p /\ \E m \in Messages :
                        (m.process = q.target /\ m.target = p) THEN 0 ELSE @]
    /\ suspect' = {q \in suspect : ~(q.target = p /\ \E m \in Messages : (m.process = q.target /\ m.target = p))}
    /\ timeout' = [q \in DOMAIN timeout |-> IF q.process = p /\ \E m \in Messages :
                        (m.process = q.target /\ m.target = p /\ q.target \in {s.target : s \in suspect})
                        THEN @ + 1 ELSE @]
    /\ localClock' = [localClock EXCEPT ![p] = IF @
                        > SendPoint /\ @ > PredictPoint /\ \A tt \in Proc : @ > timeout[p, tt]
                        THEN 0 ELSE @ + 1]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
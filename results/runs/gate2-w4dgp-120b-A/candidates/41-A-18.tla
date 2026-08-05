---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

NoSender == "nosender"
NoRecipient == "norecipient"

VARIABLES clock, timeout, lastHeard, suspected, outgoing

vars == <<clock, timeout, lastHeard, suspected, outgoing>>

MsgType == {m \in Messages : m.msgtype = "alive"}

Init ==
    /\ clock = [p \in Proc -> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ suspected = [p \in Proc |-> {}]
    /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.msgtype = "alive" /\ m.dst # p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF (clock[p] + 1) < timeout[p][q] /\ q # p THEN lastHeard[p][q] + 1 ELSE 0]]
    /\ UNCHANGED <<suspected, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF clock[p] + 1 < timeout[p][q] /\ q # p THEN lastHeard[p][q] + 1 ELSE 0]]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ \A q \in Proc : q # p => ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ \E m \in MsgType :
        /\ m.dst = p
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.src] = 0]
        /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ {m.src}]
        /\ timeout' = [timeout EXCEPT ![p][m.src] = IF m.src \in suspected[p] THEN timeout[p][m.src] + 1 ELSE timeout[p][m.src]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > Max({SendPoint, PredictPoint} \cup {timeout[p][q] : q \in Proc}) THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED <<outgoing>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in Proc : SendAlive(p))
    /\ WF_vars(\E p \in Proc : Predict(p))
    /\ WF_vars(\E p \in Proc : Receive(p))

TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ outgoing \in [Proc -> SUBSET Messages]

====
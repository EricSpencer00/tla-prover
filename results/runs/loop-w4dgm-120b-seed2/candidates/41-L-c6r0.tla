---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

AllProcs == Proc

VARIABLES suspicion, timeout, lastHeard, clock, outgoing

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

MsgType == [frm : AllProcs, to : AllProcs]

TypeOK ==
    /\ lastHeard \in [AllProcs -> [AllProcs -> 0..(2 * d0)]]
    /\ timeout \in [AllProcs -> [AllProcs -> 0..(2 * d0)]]
    /\ suspicion \in [AllProcs -> SUBSET AllProcs]
    /\ outgoing \in [AllProcs -> SUBSET MsgType]
    /\ clock \in [AllProcs -> 0..(2 * d0)]

Init ==
    /\ suspicion = [p \in AllProcs |-> {}]
    /\ timeout = [p \in AllProcs |-> [q \in AllProcs |-> d0]]
    /\ lastHeard = [p \in AllProcs |-> [q \in AllProcs |-> 0]]
    /\ clock = [p \in AllProcs |-> 0]
    /\ outgoing = [p \in AllProcs |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] =
                        { [frm |-> p, to |-> q] : q \in AllProcs } \ { [frm |-> p, to |-> p] }]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in AllProcs |-> IF lastHeard[p][q] > timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup { q \in AllProcs : lastHeard[p][q] > timeout[p][q] }]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in AllProcs |-> IF lastHeard[p][q] > timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outgoing[p] :
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {m.frm}]
        /\ lastHeard' = [lastHeard EXCEPT ![p] = [lastHeard[p] EXCEPT ![m.frm] = 0]]
        /\ timeout' = [timeout EXCEPT ![p] =
                            [timeout[p] EXCEPT ![m.frm] =
                                IF m.frm \in suspicion[p] THEN timeout[p][m.frm] + 1 ELSE timeout[p][m.frm]]]
    /\ outgoing' = [outgoing EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > d0 THEN 0 ELSE clock[p] + 1]

Next ==
    \/ \E p \in AllProcs : SendAlive(p)
    \/ \E p \in AllProcs : Predict(p)
    \/ \E p \in AllProcs : Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in AllProcs : SendAlive(p))
    /\ WF_vars(\E p \in AllProcs : Predict(p))
    /\ WF_vars(\E p \in AllProcs : Receive(p))

====
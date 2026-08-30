---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, outgoing, suspect, timeout, lastHeard

vars == <<clock, outgoing, suspect, timeout, lastHeard>>

MaxClock == SendPoint + PredictPoint + 2
MaxTimeout == SendPoint + PredictPoint + 1

TypeOK ==
    /\ clock \in [Proc -> 0..MaxClock]
    /\ outgoing \in [Proc -> SUBSET Messages]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> 1..MaxTimeout]]
    /\ lastHeard \in [Proc -> [Proc -> 0..MaxTimeout]]

Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = {m \in outgoing[p] : m.holder # p} \cup
                      {m \in Messages : m.holder = p /\ m.voter # p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |-> [r \in Proc |->
                        IF (r = p /\ lastHeard[q][r] < timeout[q][r])
                            THEN lastHeard[q][r] + 1 ELSE lastHeard[q][r]]]
    /\ UNCHANGED <<suspect, timeout>>

MakePrediction(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [q \in Proc |->
                     IF q = p THEN suspect[q]
                     ELSE suspect[q] \cup
                         {r \in Proc : r # q /\ lastHeard[q][r] > timeout[q][r]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |-> [r \in Proc |->
                        IF (r = p /\ lastHeard[q][r] < timeout[q][r])
                            THEN lastHeard[q][r] + 1 ELSE lastHeard[q][r]]]
    /\ UNCHANGED <<outgoing, timeout>>

ReceiveMsg(p) ==
    /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
    /\ \E m \in outgoing[p] :
         /\ lastHeard' = [lastHeard EXCEPT ![p][m.voter] = 0]
         /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.voter}]
         /\ timeout' = IF m.holder \in suspect[p]
                         THEN [timeout EXCEPT ![p][m.holder] = @ + 1]
                         ELSE timeout
         /\ outgoing' = [outgoing EXCEPT ![p] = outgoing[p] \ {m}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

ResetClock(p) ==
    /\ clock[p] >= MaxClock
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<outgoing, suspect, timeout, lastHeard>>

Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ MakePrediction(p)
        \/ ReceiveMsg(p)
        \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

====
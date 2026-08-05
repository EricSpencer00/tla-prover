---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # 0 /\ PredictPoint # 0
    /\ SendPoint # PredictPoint

VARIABLES
    suspicion, timeout, lastSeen, clk, toSend

vars == <<suspicion, timeout, lastSeen, clk, toSend>>

TypeOK ==
    /\ \A p \in Proc : suspicion[p] \subseteq Proc
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : lastSeen[p] \in [Proc -> Nat]
    /\ \A p \in Proc : clk[p] \in Nat
    /\ \A p \in Proc : toSend[p] \subseteq Messages

Init ==
    /\ \A p \in Proc :
        /\ suspicion[p] = {}
        /\ timeout[p] = [q \in Proc |-> d0]
        /\ lastSeen[p] = [q \in Proc |-> 0]
        /\ clk[p] = 0
        /\ toSend[p] = {}

SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ toSend' = [toSend EXCEPT ![p] = {m \in Messages : m.to = p}]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastSeen' = [lastSeen EXCEPT ![p] =
        [q \in Proc |-> IF q = p \/ lastSeen[p][q] < timeout[p][q]
                      THEN lastSeen[p][q] ELSE lastSeen[p][q] + 1]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p]
        \cup {q \in Proc : lastSeen[p][q] > timeout[p][q]}]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastSeen' = [lastSeen EXCEPT ![p] =
        [q \in Proc |-> IF q = p \/ lastSeen[p][q] < timeout[p][q]
                      THEN lastSeen[p][q] ELSE lastSeen[p][q] + 1]]
    /\ UNCHANGED <<timeout, toSend>>

Receive(p) ==
    /\ clk[p] % SendPoint # 0
    /\ clk[p] % PredictPoint # 0
    /\ \E m \in toSend[p] :
        /\ lastSeen' = [lastSeen EXCEPT ![p] = [lastSeen[p] EXCEPT ![m.to] = 0]]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {m.to}]
        /\ timeout' = [timeout EXCEPT ![p] = [timeout[p] EXCEPT
                            ![m.to] = IF m.to \in suspicion[p] THEN timeout[p][m.to] + 1 ELSE timeout[p][m.to]]]
    /\ toSend' = [toSend EXCEPT ![p] = {}]
    /\ clk' = [clk EXCEPT ![p] = IF clk[p] + 1 > SendPoint /\ clk[p] + 1 > PredictPoint
                    /\ \A q \in Proc : clk[p] + 1 > timeout[p][q] THEN 0 ELSE clk[p] + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
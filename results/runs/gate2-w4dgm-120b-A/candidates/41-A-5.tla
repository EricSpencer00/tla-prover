---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # 0 /\ PredictPoint # 0
/\ (SendPoint % PredictPoint # 0) /\ (PredictPoint % SendPoint # 0)

VARIABLES suspected, timeout, lastHeard, clk, outbox

vars == <<suspected, timeout, lastHeard, clk, outbox>>

MaxClock == 2 * Max(SendPoint, PredictPoint)

TypeOK ==
  /\ \A p \in Proc : suspected[p] \subseteq Proc
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : clk[p] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
  /\ suspected = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clk = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clk[p] % SendPoint = 0
  /\ clk[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \notin timeout[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspected, timeout>>

Predict(p) ==
  /\ clk[p] % PredictPoint = 0
  /\ clk[p] % SendPoint # 0
  /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q \in Proc : q \notin timeout[p] /\ lastHeard[p][q] > timeout[p][q]}]
  /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \notin timeout[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clk[p] % SendPoint # 0
  /\ clk[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clk' = [clk EXCEPT ![p] = IF clk[p] + 1 > MaxClock THEN 0 ELSE clk[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF \E m \in outbox[p] : m.from = q
        THEN 0
        ELSE IF q \in suspected[p] /\ \E m \in outbox[p] : m.from = q
              THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]
  /\ suspected' = [p \in Proc |-> {q \in suspected[p] : \A m \in outbox[p] : m.from # q}]
  /\ timeout' = [p \in Proc |-> [q \in Proc |-> IF q \in suspected[p] /\ \E m \in outbox[p] : m.from = q
                                      THEN timeout[p][q] + 1 ELSE timeout[p][q]]]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
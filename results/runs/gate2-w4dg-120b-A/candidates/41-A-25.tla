---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Send and predict never fire at the same clock value, so the two
\* processes are interleaved in a well-defined order.
RECURSIVE Disjoint(_, _)
Disjoint(S, T) == IF S = {} THEN TRUE
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN x \notin T /\ Disjoint(S \ {x}, T)

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send: local clock at a send multiple (not a predict multiple).
Send(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {[proc |-> q, kind |-> "alive"] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT !
                     [p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspicion, timeout>>

\* Predict: local clock at a predict multiple (not a send multiple).
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup
                     {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT !
                     [p] = [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive: default case, triggered off the send/predict multiples.
Receive(p) ==
  /\ outbox[p] = {}
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ suspicion' = [q \in Proc |->
                     IF q # p /\ lastHeard[p][q] > timeout[p][q]
                     THEN suspicion[p] \ {q} ELSE suspicion[p]]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> 0]]
  /\ timeout' = [q \in Proc |->
                   IF q # p /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint
                                        /\ \A q \in Proc : clock[p] >= timeout[p][q]
                                      THEN 0 ELSE @]

Next ==
  \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====
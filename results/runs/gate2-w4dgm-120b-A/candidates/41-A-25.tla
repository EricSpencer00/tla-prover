---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

Vars == <<suspect, timeout, lastHeard, clock, outbox>>

MaxT == 2 * d0 + 2

RECURSIVE MaxTSeen(_, _)
MaxTSeen(S, d) ==
  IF S = {} THEN d
  ELSE LET p == CHOOSE x \in S : TRUE IN
       MaxTSeen(S \ {p}, IF timeout[p] > d THEN timeout[p] ELSE d)

TypeOK ==
  /\ lastHeard \in [Proc -> 0..MaxT]
  /\ timeout \in [Proc -> 0..MaxT]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ \E msgs \in SUBSET [to : Proc, from : {p}]:
       /\ \A q \in Proc \ {p} : [to |-> q, from |-> {p}] \in msgs
       /\ outbox' = [outbox EXCEPT ![p] = msgs]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
                     IF q # p /\ lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [q \in Proc |->
                   IF q # p /\ lastHeard[q] > timeout[q] THEN suspect[q] \cup {q} ELSE suspect[q]]
  /\ lastHeard' = [q \in Proc |->
                     IF q # p /\ lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ (clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0)
  /\ \E msgs \in SUBSET [to : {p}, from : Proc]:
       /\ \A t \in msgs : outbox[t.from] = msgs
       /\ \A q \in Proc :
            /\ [to |-> p, from |-> q] \in msgs =>
                 /\ lastHeard' = [lastHeard EXCEPT ![q] = 0]
                 /\ suspect' = [suspect EXCEPT ![q] = suspect[q] \ {q}]
                 /\ timeout' = [timeout EXCEPT ![q] =
                                  IF q \in suspect[q] THEN @ + 1 ELSE @]
            /\ [to |-> p, from |-> q] \notin msgs => UNCHANGED <<lastHeard, suspect, timeout>>
       /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] =
                 IF @ >= MaxTSeen(Proc, MaxT) THEN 0 ELSE @ + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A p \in Proc : WF_Vars(SendAlive(p)) /\ WF_Vars(Predict(p)) /\ WF_Vars(Receive(p))

====
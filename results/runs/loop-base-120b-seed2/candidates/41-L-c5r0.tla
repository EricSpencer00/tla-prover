---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, last, clock, outbox

(* Helper definitions *)
IsSend(p) == (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
IsPredict(p) == (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)

MaxThreshold(p) ==
  LET tset == { timeout[p][q] : q \in Proc \ {p} } \cup { SendPoint, PredictPoint } IN
    IF tset = {} THEN 0 ELSE Max(tset)

(* Initial state *)
Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ last      = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
  /\ clock     = [p \in Proc |-> 0]
  /\ outbox    = [p \in Proc |-> {}]

(* Actions *)
Send(p) ==
  /\ IsSend(p)
  /\ outbox' = [outbox EXCEPT ![p] = { [type |-> "Alive", src |-> p, dst |-> q] : q \in Proc \ {p} }]
  /\ clock'  = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxThreshold(p) THEN 0 ELSE clock[p] + 1]
  /\ last'   = [last EXCEPT ![p][q] = IF q # p /\ last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q] | q \in Proc]
  /\ suspicion' = suspicion
  /\ timeout'   = timeout

Predict(p) ==
  /\ IsPredict(p)
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
  /\ clock'  = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxThreshold(p) THEN 0 ELSE clock[p] + 1]
  /\ last'   = [last EXCEPT ![p][q] = IF q # p /\ last[p][q] < timeout[p][q] THEN last[p][q] + 1 ELSE last[p][q] | q \in Proc]
  /\ timeout' = timeout
  /\ outbox'  = outbox

Receive(p) ==
  /\ ~IsSend(p)
  /\ ~IsPredict(p)
  /\ LET rec == { m \in UNION { outbox[q] : q \in Proc } :
                     m.dst = p /\ m.type = "Alive" } IN
     /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxThreshold(p) THEN 0 ELSE clock[p] + 1]
     /\ last'  = [last EXCEPT ![p][q] =
                    IF q \in { m.src : m \in rec } THEN 0
                    ELSE IF q # p /\ last[p][q] < timeout[p][q] THEN last[p][q] + 1
                    ELSE last[p][q] | q \in Proc]
     /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { q \in Proc : q \in { m.src : m \in rec } }]
     /\ timeout'   = [timeout EXCEPT ![p][q] =
                        IF q \in { m.src : m \in rec } /\ q \in suspicion[p] THEN timeout[p][q] + 1
                        ELSE timeout[p][q] | q \in Proc]
     /\ outbox'    = [outbox EXCEPT ![p] = {}]

ProcAction(p) == Send(p) \/ Predict(p) \/ Receive(p)

Next == \E p \in Proc : ProcAction(p)

(* Type invariant *)
TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout   \in [Proc -> [Proc -> Nat]]
  /\ last      \in [Proc -> [Proc -> Nat]]
  /\ clock     \in [Proc -> Nat]
  /\ outbox    \in [Proc -> SUBSET Messages]

====
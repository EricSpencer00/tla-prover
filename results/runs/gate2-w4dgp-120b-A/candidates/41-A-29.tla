---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, outBox

vars == <<clock, suspect, timeout, lastHeard, outBox>>

SyncProc == CHOOSE p \in Proc : TRUE

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ outBox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outBox' = [outBox EXCEPT ![p] = {m \in Messages : m.to \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc \ {p} |-> IF lastHeard[p][q] < timeout[p][q] /\ outBox[p] = {} THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc \ {p} |-> IF lastHeard[p][q] < timeout[p][q] /\ outBox[p] = {} THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outBox>>

Receive(p) ==
  /\ \/ \E q \in Proc \ {p} : \E m \in outBox[q] : m.to = p /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = @ \ {q}]
        /\ timeout' = [timeout EXCEPT ![p][q] = IF suspect[p][q] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\
                                        \A q \in Proc \ {p} : @ + 1 > timeout[p][q] THEN 0 ELSE @ + 1]
  /\ outBox' = [outBox EXCEPT ![p] = {}]
  /\ UNCHANGED <<suspect, lastHeard>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ UNCHANGED <<suspect, outBox>>
  /\ \A p \in Proc : \A q \in Proc \ {p} : lastHeard[p][q] \in Nat /\ timeout[p][q] \in Nat

====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES clock, suspicion, timeout, last, outbox

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMsg(p, q) == [type |-> "Alive", from |-> p, to |-> q]

\* Maximum timeout for a given process (used for clock reset)
MaxTimeout(p) == 
  IF Proc = {p} THEN 0
  ELSE Max({ timeout[p][q] : q \in Proc \ {p} })

\* New clock value after an action of process p
NewClock(p) ==
  LET inc == clock[p] + 1
      limit == Max({SendPoint, PredictPoint, MaxTimeout(p)})
  IN IF inc > limit THEN 0 ELSE inc

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ last = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
Send(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} }]
  /\ suspicion' = suspicion
  /\ timeout' = timeout
  /\ last' = [last EXCEPT ![p][q] = 
                IF q \in Proc \ {p} /\ last[p][q] < timeout[p][q] 
                THEN last[p][q] + 1 
                ELSE last[p][q] 
                FOR q \in Proc \ {p}]
  /\ clock' = [clock EXCEPT ![p] = NewClock(p)]

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ let newSus == { q \in Proc \ {p} : last[p][q] > timeout[p][q] } in
     /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
  /\ timeout' = timeout
  /\ outbox' = outbox
  /\ last' = [last EXCEPT ![p][q] = last[p][q] + 1 FOR q \in Proc \ {p}]
  /\ clock' = [clock EXCEPT ![p] = NewClock(p)]

Receive(p) ==
  /\ \E incMsgs \in SUBSET Messages :
        /\ \A m \in incMsgs : m.to = p /\ m.type = "Alive"
        /\ let froms == { m.from : m \in incMsgs } in
           /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ froms]
           /\ timeout' = [timeout EXCEPT ![p][q] = 
                            IF q \in froms /\ q \in suspicion[p] 
                            THEN timeout[p][q] + 1 
                            ELSE timeout[p][q] 
                            FOR q \in Proc \ {p}]
           /\ last' = [last EXCEPT ![p][q] = 
                        IF q \in froms 
                        THEN 0 
                        ELSE last[p][q] + 1 
                        FOR q \in Proc \ {p}]
           /\ outbox' = outbox
           /\ clock' = [clock EXCEPT ![p] = NewClock(p)]

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving semantics)
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Send(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clock, suspicion, timeout, last, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ \A p \in Proc : suspicion[p] \subseteq Proc \ {p}
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ \A p \in Proc : DOMAIN timeout[p] = Proc \ {p}
  /\ last \in [Proc -> [Proc -> Nat]]
  /\ \A p \in Proc : DOMAIN last[p] = Proc \ {p}
  /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* THEOREMS (optional, used by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====
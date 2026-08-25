---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspicion, timeout, lastHeard, outgoing

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MaxThreshold(p) ==
  LET T == {SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc \ {p} }
  IN IF T = {} THEN 0 ELSE CHOOSE x \in T : \A y \in T : y <= x

NextClock(p, c) ==
  IF c + 1 > MaxThreshold(p) THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ clock      = [p \in Proc |-> 0]
  /\ suspicion  = [p \in Proc |-> {}]
  /\ timeout    = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ lastHeard  = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outgoing   = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send action (alive messages)
\* ----------------------------------------------------------------------
Send(p) ==
  /\ p \in Proc
  /\ \E k \in Nat : clock[p] = SendPoint * k
  /\ ~(\E j \in Nat : clock[p] = PredictPoint * j)        \* not a predict step
  /\ outgoing' = [outgoing EXCEPT ![p] = 
        { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} } ]
  /\ suspicion' = suspicion
  /\ timeout'   = timeout
  /\ clock'     = [clock EXCEPT ![p] = NextClock(p, clock[p])]
  /\ lastHeard' = [lastHeard EXCEPT 
        ![p] = [q \in Proc |-> 
                IF q # p /\ lastHeard[p][q] < timeout[p][q] 
                THEN lastHeard[p][q] + 1 
                ELSE lastHeard[p][q] ]]

\* ----------------------------------------------------------------------
\* Predict action (suspicion update)
\* ----------------------------------------------------------------------
Predict(p) ==
  /\ p \in Proc
  /\ \E j \in Nat : clock[p] = PredictPoint * j
  /\ ~(\E k \in Nat : clock[p] = SendPoint * k)          \* not a send step
  /\ suspicion' = [suspicion EXCEPT 
        ![p] = suspicion[p] \cup 
               { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } ]
  /\ timeout'   = timeout
  /\ outgoing'  = outgoing
  /\ clock'     = [clock EXCEPT ![p] = NextClock(p, clock[p])]
  /\ lastHeard' = [lastHeard EXCEPT 
        ![p] = [q \in Proc |-> 
                IF q # p /\ lastHeard[p][q] < timeout[p][q] 
                THEN lastHeard[p][q] + 1 
                ELSE lastHeard[p][q] ]]

\* ----------------------------------------------------------------------
\* Receive action (processes receive a (possibly empty) set of alive msgs)
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Proc
  /\ \E R \in SUBSET (Proc \ {p}) :
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ R]
        /\ outgoing'  = outgoing
        /\ timeout'   = [timeout EXCEPT 
               ![p] = [q \in Proc |-> 
                       IF q \in R /\ q \in suspicion[p] 
                       THEN timeout[p][q] + 1 
                       ELSE timeout[p][q] ]]
        /\ lastHeard' = [lastHeard EXCEPT 
               ![p] = [q \in Proc |-> 
                       IF q \in R THEN 0 ELSE lastHeard[p][q] ]]
        /\ clock'     = [clock EXCEPT ![p] = NextClock(p, clock[p])]

\* ----------------------------------------------------------------------
\* Next-state relation (any process may take one of the three actions)
\* ----------------------------------------------------------------------
Next ==
  \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ clock      \in [Proc -> Nat]
  /\ suspicion  \in [Proc -> SUBSET Proc]
  /\ timeout    \in [Proc -> [Proc -> Nat]]
  /\ lastHeard  \in [Proc -> [Proc -> Nat]]
  /\ outgoing   \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [] [Next]_<<clock, suspicion, timeout, lastHeard, outgoing>>

\* ----------------------------------------------------------------------
\* Additional properties (placeholder)
\* ----------------------------------------------------------------------
PROPERTIES == TRUE

====
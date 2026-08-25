---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, last, clock, outMsgs

\* ----------------------------------------------------------------------
\*  Type definitions
\* ----------------------------------------------------------------------
Message == [src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock   = [p \in Proc |-> 0]
    /\ outMsgs = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
SendNow(p) == clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
PredictNow(p) == clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
ResetClock(c) == IF c + 1 > SendPoint /\ c + 1 > PredictPoint THEN 0 ELSE c + 1

AliveMsg(i,j) == [src |-> i, dst |-> j]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
SendAlive(i) ==
    /\ SendNow(i)
    /\ outMsgs' = [outMsgs EXCEPT ![i] = { AliveMsg(i,j) : j \in Proc \ {i} }]
    /\ clock'   = [clock EXCEPT ![i] = ResetClock(clock[i])]
    /\ last'    = [last EXCEPT ![i] = 
                    [j \in Proc |-> 
                        IF j # i /\ last[i][j] < timeout[i][j] 
                        THEN last[i][j] + 1 
                        ELSE last[i][j]]]
    /\ UNCHANGED << suspect, timeout >>

Predict(i) ==
    /\ PredictNow(i)
    /\ suspect' = [suspect EXCEPT ![i] = 
                    suspect[i] \cup
                    { j \in Proc \ {i} : last[i][j] > timeout[i][j] }]
    /\ clock'   = [clock EXCEPT ![i] = ResetClock(clock[i])]
    /\ last'    = [last EXCEPT ![i] = 
                    [j \in Proc |-> 
                        IF j # i /\ last[i][j] < timeout[i][j] 
                        THEN last[i][j] + 1 
                        ELSE last[i][j]]]
    /\ UNCHANGED << timeout, outMsgs >>

Receive(i) ==
    /\ \lnot SendNow(i)
    /\ \lnot PredictNow(i)
    /\ LET senders == { j \in Proc \ {i} : AliveMsg(j,i) \in outMsgs[j] } IN
       \E rec \subseteq senders :
          /\ last' = [last EXCEPT ![i] = 
                        [j \in Proc |-> 
                            IF j \in rec THEN 0 ELSE last[i][j] + 1]]
          /\ suspect' = [suspect EXCEPT ![i] = suspect[i] \ rec]
          /\ timeout' = [timeout EXCEPT ![i] = 
                         [j \in Proc |-> 
                            IF j \in rec /\ j \in suspect[i] 
                            THEN timeout[i][j] + 1 
                            ELSE timeout[i][j]]]
          /\ clock' = [clock EXCEPT ![i] = ResetClock(clock[i])]
          /\ UNCHANGED outMsgs

Next ==
    \/ \E i \in Proc : SendAlive(i)
    \/ \E i \in Proc : Predict(i)
    \/ \E i \in Proc : Receive(i)

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspect, timeout, last, clock, outMsgs>>

\* ----------------------------------------------------------------------
\*  Invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspect[p] \subseteq Proc \ {p}
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : timeout[p][q] \in Nat
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : last[p][q] \in Nat
    /\ clock \in [Proc -> Nat]
    /\ outMsgs \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\*  Theorem (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====
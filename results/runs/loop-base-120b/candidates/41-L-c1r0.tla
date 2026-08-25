---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,            \* Set of process identifiers
    d0,              \* Default timeout interval (positive Nat)
    SendPoint,       \* Send interval (positive Nat)
    PredictPoint,    \* Predict interval (positive Nat)
    Messages         \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  (process p's suspicion set)
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] (timeout interval p uses for q)
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] (ticks since p last heard from q)
    clk,         \* [p \in Proc |-> Nat] (local clock of each process)
    outbox       \* [p \in Proc |-> SUBSET Messages] (messages p wants to send)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The maximum timeout value observed by a process p
MaxTimeout(p) ==
    IF Proc = {} THEN 0
    ELSE Max({ timeout[p][q] : q \in Proc })

\* The maximal relevant threshold for resetting the clock of p
MaxClock(p) == Max({SendPoint, PredictPoint} \cup { MaxTimeout(p) })

\* Next value of the local clock for process p
NextClk(p) ==
    IF clk[p] + 1 > MaxClock(p) THEN 0 ELSE clk[p] + 1

\* Condition for a Send action (multiple of SendPoint, not of PredictPoint)
SendCond(p) ==
    (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)

\* Condition for a Predict action (multiple of PredictPoint, not of SendPoint)
PredictCond(p) ==
    (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send alive messages
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ SendCond(p)
    /\ \* Create an alive message for every other process
       let newMsgs == { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} } in
       outbox' = [outbox EXCEPT ![p] = outbox[p] \cup newMsgs]
    /\ \* Increment counters for processes that have not yet timed out
       lastHeard' = [lastHeard EXCEPT
                     ![p][q] = IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                 THEN lastHeard[p][q] + 1
                                 ELSE lastHeard[p][q]
                     \FORALL q \in Proc]
    /\ clk' = [clk EXCEPT ![p] = NextClk(p)]
    /\ UNCHANGED <<suspicion, timeout>>

\* ----------------------------------------------------------------------
\* Predict (update suspicion set)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ PredictCond(p)
    /\ \* Add to suspicion any process whose counter exceeds its timeout
       let newSuspects == { q \in Proc \ {p} :
                              lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
    /\ \* Increment all last‑heard counters (including those already timed‑out)
       lastHeard' = [lastHeard EXCEPT
                     ![p][q] = lastHeard[p][q] + 1
                     \FORALL q \in Proc \ {p}]
    /\ clk' = [clk EXCEPT ![p] = NextClk(p)]
    /\ UNCHANGED <<timeout, outbox>>

\* ----------------------------------------------------------------------
\* Receive incoming alive messages
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ ~SendCond(p) /\ ~PredictCond(p)
    /\ \* Nondeterministically choose the set of processes from which p receives an alive message
       \E Q \subseteq Proc \ {p} :
          /\ \* For each q in Q we assume an alive message from q was received
             (* Reset last‑heard counter and remove q from suspicion *)
             lastHeard' = [lastHeard EXCEPT
                           ![p][q] = 0
                           \FORALL q \in Q]
             /\ suspicion' = [suspicion EXCEPT
                               ![p] = suspicion[p] \ Q]
             /\ \* Adaptive timeout: if q was suspected before reception, increase its timeout
                timeout' = [timeout EXCEPT
                             ![p][q] = IF q \in Q /\ q \in suspicion[p]
                                         THEN timeout[p][q] + 1
                                         ELSE timeout[p][q]
                             \FORALL q \in Q]
             /\ outbox' = outbox   \* No change to the sending buffer
             /\ clk' = [clk EXCEPT ![p] = NextClk(p)]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<suspicion, timeout, lastHeard, clk, outbox>>

Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clk       \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Additional (placeholder) properties
\* ----------------------------------------------------------------------
Properties == TRUE

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
=============================================================================
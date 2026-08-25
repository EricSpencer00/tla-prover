---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Period (in ticks) for sending alive messages
    PredictPoint,  \* Period (in ticks) for making predictions
    Messages       \* Set of possible messages

(*-------------------------------------------------------------------*)
(* Message definition *)
Msg == [type : {"alive"}, src : Proc, dst : Proc]

(*-------------------------------------------------------------------*)
VARIABLES
    clock,        \* [p \in Proc -> Nat]  local clock per process
    timeout,      \* [p \in Proc -> [q \in Proc -> Nat]]  adaptive timeout intervals
    lastHeard,    \* [p \in Proc -> [q \in Proc -> Nat]]  ticks since last alive from q
    suspicion,   \* [p \in Proc -> SUBSET Proc]          set of suspected processes
    outbox        \* [p \in Proc -> SUBSET Msg]          messages a process intends to send

vars == <<clock, timeout, lastHeard, suspicion, outbox>>

(*-------------------------------------------------------------------*)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]

(*-------------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0               \* send and predict never coincide
    /\ outbox' = [outbox EXCEPT ![p] = 
                     { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                       [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, suspicion>>

(*-------------------------------------------------------------------*)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                       suspicion[p] \cup 
                       { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                       [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outbox>>

(*-------------------------------------------------------------------*)
\* Helper to collect all messages currently in any outbox
AllMsgs == UNION { outbox[p] : p \in Proc }

Receive ==
    /\ \A p \in Proc :
          LET recv == { m \in AllMsgs : m.dst = p } IN
          /\ lastHeard' = [lastHeard EXCEPT 
                ![p] = [ q \in Proc |-> 
                          IF q \in { m.src : m \in recv } 
                              THEN 0 
                              ELSE lastHeard[p][q] + 1 ]]
          /\ suspicion' = [suspicion EXCEPT 
                ![p] = suspicion[p] \ { m.src : m \in recv }]
          /\ timeout' = [timeout EXCEPT 
                ![p] = [ q \in Proc |-> 
                          IF q \in { m.src : m \in recv } /\ q \in suspicion[p] 
                              THEN timeout[p][q] + 1 
                              ELSE timeout[p][q] ]]
    /\ outbox' = [p \in Proc |-> {}]          \* all messages are delivered
    /\ clock' = [clock EXCEPT ![p] = 
                    IF clock[p] + 1 > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
                       THEN 0 
                       ELSE clock[p] + 1]

(*-------------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ Receive

(*-------------------------------------------------------------------*)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Msg]

(*-------------------------------------------------------------------*)
SPECIFICATION == Init /\ [][Next]_vars

INVARIANTS == TypeOK

PROPERTIES == TRUE

====
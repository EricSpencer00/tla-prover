---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,          \* Set of all processes
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (at least includes the alive messages)

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)

AliveMsg(p) == [type |-> "Alive", sender |-> p]

MsgType == {"Alive"}

Variable
    suspicion,   \* [p \in Proc -> SUBSET Proc] : processes p currently suspects
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] : timeout interval p uses for q
    lastHeard,   \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since p last heard from q
    clock,       \* [p \in Proc -> Nat] : local logical clock of p
    outbox       \* [p \in Proc -> SUBSET Messages] : messages p intends to send this step

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

(* ------------------------------------------------------------------------ *)
(* Initialization                                                          *)
(* ------------------------------------------------------------------------ *)

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Actions                                                                 *)
(* ------------------------------------------------------------------------ *)

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {AliveMsg(p)} \cup outbox[p]]
    /\ \A q \in Proc :
         IF q # p /\ clock[p] % timeout[p][q] # 0
         THEN lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
         ELSE UNCHANGED lastHeard
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
           suspicion[p] \cup
           { q \in Proc : 
               q # p /\ lastHeard[p][q] >= timeout[p][q] }]
    /\ \A q \in Proc :
         IF q # p
         THEN lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
         ELSE UNCHANGED lastHeard
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~ (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ LET incoming == { m \in outbox[q] : q \in Proc /\ m.type = "Alive" /\ m.sender = q } IN
       /\ \A m \in incoming :
            /\ let sender == m.sender in
               /\ lastHeard' = [lastHeard EXCEPT ![p][sender] = 0]
               /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {sender}]
               /\ IF sender \in suspicion[p]
                  THEN timeout' = [timeout EXCEPT ![p][sender] = @ + 1]
                  ELSE UNCHANGED timeout
       /\ clock' = [clock EXCEPT ![p] = 
               IF @ + 1 > Max({SendPoint, PredictPoint} \cup 
                              {timeout[p][q] : q \in Proc})
               THEN 0 ELSE @ + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ UNCHANGED suspicion

Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------ *)
(* Type invariant (named TypeOK as required)                               *)
(* ------------------------------------------------------------------------ *)

TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

(* ------------------------------------------------------------------------ *)
(* Theorem (optional, but useful)                                           *)
(* ------------------------------------------------------------------------ *)

THEOREM Spec => []TypeOK

====
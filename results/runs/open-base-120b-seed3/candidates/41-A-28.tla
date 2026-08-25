---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

(*-------------------------------------------------------------------*)
(* CONSTANTS *)
CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of possible messages (used by the environment)

(*-------------------------------------------------------------------*)
(* MESSAGE DEFINITION *)
Message == [src : Proc, dst : Proc, type : {"Alive"}]

(*-------------------------------------------------------------------*)
(* STATE VARIABLES *)
VARIABLES 
    Suspect,   \* [p \in Proc |-> SUBSET Proc]   -- suspicion set per process
    Timeout,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout per (p,q)
    Last,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last heard
    Clock,     \* [p \in Proc |-> Nat]                     -- local clock per process
    Out        \* [p \in Proc |-> SUBSET Message]          -- outgoing messages per process

vars == <<Suspect, Timeout, Last, Clock, Out>>

(*-------------------------------------------------------------------*)
(* HELPER DEFINITIONS *)

IsSend(p) == 
    (Clock[p] % SendPoint = 0) /\ (Clock[p] % PredictPoint # 0)

IsPredict(p) == 
    (Clock[p] % PredictPoint = 0) /\ (Clock[p] % SendPoint # 0)

IsReceive(p) == 
    ~IsSend(p) /\ ~IsPredict(p)

MaxTimeout(p) == 
    MAX { Timeout[p][q] : q \in Proc }

NextClock(p, t) == 
    LET newVal == Clock[p] + 1 IN
    IF newVal > Max({SendPoint, PredictPoint, MaxTimeout(p)}) 
        THEN 0 
        ELSE newVal

(*-------------------------------------------------------------------*)
(* INITIAL STATE *)

Init == 
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ Last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock   = [p \in Proc |-> 0]
    /\ Out     = [p \in Proc |-> {}]

(*-------------------------------------------------------------------*)
(* ACTIONS *)

(* SEND ACTION *)
Send(p) == 
    /\ IsSend(p)
    /\ Out' = [Out EXCEPT ![p] = 
                { [src |-> p, dst |-> q, type |-> "Alive"] : q \in Proc \ {p} }]
    /\ Clock' = [Clock EXCEPT ![p] = NextClock(p, Clock[p])]
    /\ \A q \in Proc \ {p} :
          IF Last[p][q] < Timeout[p][q] 
          THEN Last' = [Last EXCEPT ![p][q] = Last[p][q] + 1]
          ELSE UNCHANGED <<Last>>
    /\ UNCHANGED <<Suspect, Timeout>>

(* PREDICT ACTION *)
Predict(p) == 
    /\ IsPredict(p)
    /\ Suspect' = [Suspect EXCEPT ![p] = 
          Suspect[p] \cup { q \in Proc \ {p} : Last[p][q] >= Timeout[p][q] }]
    /\ Clock' = [Clock EXCEPT ![p] = NextClock(p, Clock[p])]
    /\ Last' = [Last EXCEPT ![p] = 
          [q \in Proc |-> IF q = p THEN 0 ELSE Last[p][q] + 1]]
    /\ UNCHANGED <<Timeout, Out>>

(* RECEIVE ACTION *)
Receive(p) == 
    /\ IsReceive(p)
    /\ \* Messages that the environment delivers to p in this step
       \* (the controller chooses any subset of Messages addressed to p)
       \E del \in SUBSET Messages :
           /\ \A m \in del : 
                /\ m.type = "Alive"
                /\ m.dst = p
                /\ m.src \in Proc
           /\ \* Update for each source that sent an alive message
              LET sources == { m.src : m \in del } IN
              /\ Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \ { q \in sources }]
              /\ Last' = [Last EXCEPT ![p] = 
                         [q \in Proc |-> IF q \in sources THEN 0 ELSE Last[p][q]]]
              /\ Timeout' = [Timeout EXCEPT ![p] = 
                         [q \in Proc |-> IF q \in sources /\ q \in Suspect[p] 
                                        THEN Timeout[p][q] + 1 
                                        ELSE Timeout[p][q]]]
              /\ Clock' = [Clock EXCEPT ![p] = NextClock(p, Clock[p])]
              /\ Out' = [Out EXCEPT ![p] = {}]  \* after processing, outgoing set is cleared
    /\ UNCHANGED <<>>

(* COMBINED ACTION FOR ONE PROCESS *)
ProcessStep(p) == Send(p) \/ Predict(p) \/ Receive(p)

(* NEXT STATE RELATION *)
Next == 
    \E p \in Proc : ProcessStep(p)

(*-------------------------------------------------------------------*)
(* SPECIFICATION *)

SPECIFICATION == Init /\ [][Next]_vars

(*-------------------------------------------------------------------*)
(* INVARIANTS *)

TypeOK == 
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : p \notin Suspect[p]   \* a process never suspects itself
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : 
          (q = p => Timeout[p][q] = 0) 
          /\ (q # p => Timeout[p][q] >= 0)
    /\ Last \in [Proc -> [Proc -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Out \in [Proc -> SUBSET Message]

INVARIANTS == TypeOK

(*-------------------------------------------------------------------*)
(* PROPERTIES *)

PROPERTIES == TRUE

====
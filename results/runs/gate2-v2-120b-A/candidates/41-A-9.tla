---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

(* ----------------------------------------------------------------------
   Constants (to be bound in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Proc,          \* Set of all processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible alive messages

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
AliveMsg == [type : "Alive", from : Proc, to : Proc]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES
    clock,          \* [p \in Proc -> Nat], local clock per process
    suspicion,      \* [p \in Proc -> SUBSET Proc], suspected processes per process
    timeout,        \* [p \in Proc -> [q \in Proc -> Nat]], timeout interval per (p,q)
    lastHeard,      \* [p \in Proc -> [q \in Proc -> Nat]], ticks since last alive from q as seen by p
    outMsgs         \* [p \in Proc -> SUBSET AliveMsg], outgoing messages per process

vars == <<clock, suspicion, timeout, lastHeard, outMsgs>>

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
AllProcs == Proc

(* Validity of a message *)
IsAlive(m) == m.type = "Alive"

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outMsgs = [p \in Proc |-> {}]

(* ----------------------------------------------------------------------
   Process actions (one process at a time)
   ---------------------------------------------------------------------- *)

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0            \* send and predict never coincide
    /\ outMsgs' = [outMsgs EXCEPT ![p] = 
          { [type |-> "Alive", from |-> p, to |-> q] : q \in Proc }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
          ![p][q] = IF timeout[p][q] # 0 THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
          \* increment counters for all q; they will be reset on receive
        ]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT 
          ![p] = suspicion[p] \cup
            { q \in Proc : lastHeard[p][q] >= timeout[p][q] }
        ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
          ![p][q] = lastHeard[p][q] + 1
        ]
    /\ outMsgs' = outMsgs
    /\ UNCHANGED timeout

Receive(p) ==
    /\ \E m \in outMsgs[[q \in Proc]] : 
         /\ m.to = p
         /\ m.type = "Alive"
         /\ m.from \in Proc
    /\ LET senders == { m.from : 
            \E q \in Proc : m \in outMsgs[q] /\ m.to = p /\ m.type = "Alive"} IN
       /\ IF senders # {} THEN 
            /\ lastHeard' = [lastHeard EXCEPT 
                  ![p][s] = IF s \in senders THEN 0 ELSE lastHeard[p][s] 
               ]
            /\ suspicion' = [suspicion EXCEPT 
                  ![p] = suspicion[p] \ { s : s \in senders } 
               ]
            /\ timeout' = [timeout EXCEPT 
                  ![p][s] = IF s \in senders /\ s \in suspicion[p] 
                             THEN timeout[p][s] + 1 
                             ELSE timeout[p][s] 
               ]
         ELSE 
            /\ UNCHANGED <<suspicion, timeout, lastHeard>>
    /\ clock' = [clock EXCEPT ![p] = 0]   \* reset local clock after receive
    /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]   \* clear sent messages after they have been "delivered"

Other(p) ==
    /\ clock[p] >= SendPoint
    /\ clock[p] >= PredictPoint
    /\ \A q \in Proc : clock[p] >= timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastHeard>>

(* ----------------------------------------------------------------------
   NEXT relation: one process takes one atomic step
   ---------------------------------------------------------------------- *)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)
        \/ Other(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Type invariant (named TypeOK as required)
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outMsgs \in [Proc -> SUBSET AliveMsg]

====
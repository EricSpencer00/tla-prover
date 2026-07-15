---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval
    SendPoint,     \* Positive integer, send interval
    PredictPoint,  \* Positive integer, predict interval
    Messages       \* Set of possible message records

(* ------------------------------------------------------------------------ *)
(* Message definition                                                       *)
(*   An alive message is a record with fields "type" (always "alive")      *)
(*   and "src" indicating the sending process.                             *)
(* ------------------------------------------------------------------------ *)
MsgAlive(p) == [type |-> "alive", src |-> p]

(* ------------------------------------------------------------------------ *)
(* Derived sets                                                             *)
(* ------------------------------------------------------------------------ *)
MsgSet == { m \in Messages : m.type = "alive" }

(* ------------------------------------------------------------------------ *)
(* Variables                                                                *)
(*   suspicion[p] : set of processes that p currently suspects               *)
(*   timeout[p][q] : integer timeout interval p uses for q                 *)
(*   counter[p][q] : ticks since p last heard from q                        *)
(*   clock[p] : local clock of p                                            *)
(*   out[p] : set of messages p will send in the current step              *)
(* ------------------------------------------------------------------------ *)
VARIABLES suspicion, timeout, counter, clock, out

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)
NotTimedOut(p, q) == counter[p][q] <= timeout[p][q]

(* ------------------------------------------------------------------------ *)
(* Initialization                                                            *)
(* ------------------------------------------------------------------------ *)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ counter   = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------ *)
(* Send Alive action for a single process p                                 *)
(* ------------------------------------------------------------------------ *)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { MsgAlive(p) } \cup out[p]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ counter' = [counter EXCEPT
        ![p][q] = IF q = p THEN @
                  ELSE IF NotTimedOut(p, q) THEN @ + 1
                  ELSE @ ]
    /\ UNCHANGED <<suspicion, timeout>>

(* ------------------------------------------------------------------------ *)
(* Predict action for a single process p                                    *)
(* ------------------------------------------------------------------------ *)
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
        ![p] = suspicion[p] \cup
                { q \in Proc : q # p /\ counter[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ counter' = [counter EXCEPT
        ![p][q] = IF q = p THEN @
                  ELSE @ + 1]
    /\ out' = out
    /\ UNCHANGED timeout

(* ------------------------------------------------------------------------ *)
(* Receive action for a single process p                                    *)
(* ------------------------------------------------------------------------ *)
Receive(p) ==
    /\ \E msgs \in out : \A m \in msgs :
           /\ m.type = "alive"
           /\ m.src \in Proc
    /\ LET incoming == { m \in out[p] : m.type = "alive" } IN
       /\ \A m \in incoming :
            /\ counter' = [counter EXCEPT ![p][m.src] = 0]
            /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { m.src }]
            /\ timeout' =
               IF m.src \in suspicion[p]
               THEN [timeout EXCEPT ![p][m.src] = @ + 1]
               ELSE timeout
       /\ clock' = [clock EXCEPT ![p] = @ + 1]
       /\ out' = [out EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, counter>>

(* ------------------------------------------------------------------------ *)
(* Clock reset action for a single process p (ensures finite domain)       *)
(* ------------------------------------------------------------------------ *)
ResetClock(p) ==
    /\ clock[p] > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, timeout, counter, out>>

(* ------------------------------------------------------------------------ *)
(* Choice of which process acts in a step                                   *)
(* ------------------------------------------------------------------------ *)
ProcStep ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)
        \/ ResetClock(p)

Next == ProcStep

(* ------------------------------------------------------------------------ *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<suspicion, timeout, counter, clock, out>>

(* ------------------------------------------------------------------------ *)
(* Type correctness invariant                                               *)
(* ------------------------------------------------------------------------ *)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ counter \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

(* ------------------------------------------------------------------------ *)
(* Theorems (optional, can be used by TLC)                                   *)
(* ------------------------------------------------------------------------ *)
THEOREM Spec => []TypeOK

====
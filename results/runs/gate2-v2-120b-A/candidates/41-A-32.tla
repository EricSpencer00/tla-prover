---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

CONSTANTS
    Proc,          \* Set of all processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (will be defined below)

(* Message type: an alive message from a sender to a receiver *)
Message == [type : {"Alive"}, from : Proc, to : Proc]

VARIABLES
    suspicion,   \* [proc \in Proc |-> SUBSET Proc]   -- processes each proc suspects
    timeout,     \* [proc \in Proc |-> [p \in Proc |-> Nat]]  -- timeout interval per pair
    lastHeard,   \* [proc \in Proc |-> [p \in Proc |-> Nat]]  -- ticks since last alive from p
    clock,       \* [proc \in Proc |-> Nat]          -- local clock per process
    outMsgs      \* [proc \in Proc |-> SUBSET Messages]  -- outgoing messages per proc

(* -------------------------------------------------------------------------- *)
(* Helper definitions *)
IsSendStep(p)   == /\ clock[p] % SendPoint = 0
                    /\ clock[p] % PredictPoint # 0

IsPredictStep(p) == /\ clock[p] % PredictPoint = 0
                    /\ clock[p] % SendPoint # 0

IsIdleStep(p)   == /\ clock[p] % SendPoint # 0
                    /\ clock[p] % PredictPoint # 0

AllSameTimeout(p) == \A q \in Proc : timeout[p][q] >= 1
AllClocksInRange(p) == clock[p] <= Max(SendPoint, PredictPoint, \A q \in Proc : timeout[p][q])

(* -------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outMsgs   = [p \in Proc |-> {}]

(* -------------------------------------------------------------------------- *)
(* Actions *)

(* Send alive messages to every other process *)
Send(p) ==
    /\ IsSendStep(p)
    /\ outMsgs' = [outMsgs EXCEPT ![p] = { [type |-> "Alive", from |-> p, to |-> q] : q \in Proc \ {p} }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q = p THEN 0
                        ELSE IF outMsgs[p] = {} THEN lastHeard[p][q] + 1
                        ELSE lastHeard[p][q]]
    /\ UNCHANGED <<suspicion, timeout>>

(* Predict which processes have timed out *)
Predict(p) ==
    /\ IsPredictStep(p)
    /\ LET timedOut == { q \in Proc : q # p /\ lastHeard[p][q] >= timeout[p][q] } IN
       /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup timedOut]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q \in timedOut THEN lastHeard[p][q] + 1
                        ELSE lastHeard[p][q] + 1]
    /\ UNCHANGED <<timeout, outMsgs>>

(* Receive incoming alive messages *)
Receive(p) ==
    /\ IsIdleStep(p)
    /\ LET incoming == { m \in outMsgs[q] : q \in Proc /\ m.to = p /\ m.type = "Alive" } IN
       /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF \E m \in incoming : m.from = q THEN 0
                        ELSE lastHeard[p][q] + 1]
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                        { q \in suspicion[p] : \E m \in incoming : m.from = q }]
    /\ timeout' = [timeout EXCEPT 
                    ![p][q] = 
                        IF \E m \in incoming : m.from = q THEN timeout[p][q] + 1
                        ELSE timeout[p][q]]
    /\ clock' = [clock EXCEPT ![p] = 
                    IF clock[p] >= Max(SendPoint, PredictPoint, \A q \in Proc : timeout[p][q])
                    THEN 0
                    ELSE clock[p] + 1]
    /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastHeard>>

(* Next-state relation: exactly one process takes a step *)
Next ==
    \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

(* The specification: Init plus stuttering closure of Next *)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outMsgs>>

(* -------------------------------------------------------------------------- *)
(* Safety invariant: type correctness *)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outMsgs   \in [Proc -> SUBSET Messages]

(* -------------------------------------------------------------------------- *)
(* Export the specification name expected by the .cfg *)
InitSpec == Init
NextSpec == Next

=============================================================================
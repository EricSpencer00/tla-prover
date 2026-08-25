---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ---------------------------------------------------------------------- *)
(* CONSTANTS *)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages

(* ---------------------------------------------------------------------- *)
(* MESSAGE DEFINITION *)
Message == [type : {"alive"}, from : Proc, to : Proc]

ASSUME Messages = Message

(* ---------------------------------------------------------------------- *)
(* VARIABLES *)
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  -- set of processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout per peer
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]                -- local clock per process
    outbox       \* [p \in Proc |-> SUBSET Message]    -- messages p wants to send

vars == << suspicion, timeout, lastHeard, clock, outbox >>

(* ---------------------------------------------------------------------- *)
(* INITIAL STATE *)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(* ---------------------------------------------------------------------- *)
(* HELPERS *)
SendReady(p) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

PredictReady(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

\* Increment counters for all peers that have not yet timed‑out
IncCounters(prev) ==
    [p \in Proc |-> 
        [q \in Proc |-> 
            IF prev[p][q] < timeout[p][q] 
                THEN prev[p][q] + 1 
                ELSE prev[p][q]]]

(* ---------------------------------------------------------------------- *)
(* ACTION: SEND ALIVE MESSAGES *)
Send(p) ==
    /\ SendReady(p)
    /\ LET newMsgs == { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} }
       IN outbox' = [outbox EXCEPT ![p] = outbox[p] \cup newMsgs]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(lastHeard)[p]]
    /\ UNCHANGED << suspicion, timeout >>

(* ---------------------------------------------------------------------- *)
(* ACTION: MAKE PREDICTION *)
Predict(p) ==
    /\ PredictReady(p)
    /\ LET newSuspects == { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }
       IN suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(lastHeard)[p]]
    /\ UNCHANGED << timeout, outbox >>

(* ---------------------------------------------------------------------- *)
(* ACTION: RECEIVE MESSAGES *)
Receive(p) ==
    /\ ~SendReady(p)
    /\ ~PredictReady(p)
    \* Choose nondeterministically the set of senders whose alive message is received
    \* (any subset of Proc \\ {p})
    LET R == CHOOSE S \in SUBSET (Proc \ {p}) : TRUE
        updLast(q) ==
            IF q \in R THEN 0
            ELSE IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1
            ELSE lastHeard[p][q]
        updTimeout(q) ==
            IF q \in R /\ q \in suspicion[p] THEN timeout[p][q] + 1
            ELSE timeout[p][q]
        updSuspect == suspicion[p] \ R
    IN /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> updLast(q)]]
       /\ timeout'   = [timeout   EXCEPT ![p] = [q \in Proc |-> updTimeout(q)]]
       /\ suspicion' = [suspicion EXCEPT ![p] = updSuspect]
       /\ outbox'    = outbox
       /\ clock'     = clock

(* ---------------------------------------------------------------------- *)
(* NEXT STATE RELATION *)
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

(* ---------------------------------------------------------------------- *)
(* SPECIFICATION *)
Spec == Init /\ [] [Next]_vars

(* ---------------------------------------------------------------------- *)
(* TYPE INVARIANT *)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

(* ---------------------------------------------------------------------- *)
(* ASSUMPTIONS ON INTERVALS *)
ASSUME SendPoint > 0
ASSUME PredictPoint > 0
ASSUME SendPoint # PredictPoint
ASSUME \A n \in Nat : (n > 0) => ~(SendPoint % n = 0 /\ PredictPoint % n = 0) \* not multiples (simplified)

(* ---------------------------------------------------------------------- *)
(* THEOREMS / PROPERTIES *)
THEOREM SpecTypeOK == Spec => []TypeOK

====
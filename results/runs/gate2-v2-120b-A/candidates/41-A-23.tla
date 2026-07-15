---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,           \* The set of all processes
    d0,             \* Default timeout interval (positive integer)
    SendPoint,      \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,   \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages        \* Set of all possible messages (should contain Alive(p) for all p)

(* ------------------------------------------------------------------------- *)
(* Message definition *)
Message == [type : {"Alive"}, src : Proc]

(* ------------------------------------------------------------------------- *)
(* Variables *)
VARIABLES
    suspicion,      \* [p \in Proc |-> SUBSET Proc] : set of processes p suspects
    timeout,        \* [p \in Proc |-> [q \in Proc |-> Nat]] : adaptive timeout for each pair
    lastHeard,      \* [p \in Proc |-> [q \in Proc |-> Nat]] : ticks since p last heard from q
    clock,          \* [p \in Proc |-> Nat] : local clock of each process
    outbox          \* [p \in Proc |-> SUBSET Message] : messages p intends to send

(* For convenience, define the set of all alive messages *)
AliveMsg(p) == [type |-> "Alive", src |-> p]

(* ------------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(* ------------------------------------------------------------------------- *)
(* Helper predicates *)
IsSend(clock[p]) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

IsPredict(clock[p]) == 
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

(* ------------------------------------------------------------------------- *)
(* Actions *)

SendAlive(p) ==
    /\ clock[p] \in Nat
    /\ IsSend(clock[p])
    /\ outbox' = [outbox EXCEPT ![p] = {AliveMsg(q) : q \in Proc \ {p}}]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
            IF q \in Proc \ {p} /\ lastHeard[p][q] < timeout[p][q] 
               THEN @ + 1 
               ELSE @]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] \in Nat
    /\ IsPredict(clock[p])
    /\ (* add to suspicion those q where lastHeard exceeds timeout *)
       suspicion' = [suspicion EXCEPT ![p] = 
            suspicion[p] \cup { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1 
            \* (the same increment as in SendAlive for all q)
            ]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] \in Nat
    /\ ~IsSend(clock[p]) /\ ~IsPredict(clock[p])
    /\ outbox' = [outbox EXCEPT ![p] = {}]   \* all pending messages are considered sent
    /\ clock'   = [clock EXCEPT ![p] = 
            IF clock[p] >= Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
               THEN 0
               ELSE @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
            IF q \in Proc /\ 
               (\E m \in outbox[q] : m.type = "Alive" /\ m.src = q) 
               THEN 0
               ELSE @ + 1]
    /\ suspicion' = [suspicion EXCEPT ![p][q] = 
            IF q \in Proc /\ 
               (\E m \in outbox[q] : m.type = "Alive" /\ m.src = q) 
               THEN {} 
               ELSE @]
    /\ timeout' = [timeout EXCEPT 
            ![p][q] = 
                IF q \in Proc /\ 
                   (\E m \in outbox[q] : m.type = "Alive" /\ m.src = q) /\ q \in suspicion[p]
                   THEN @ + 1
                   ELSE @]
    /\ UNCHANGED <<>>

(* ------------------------------------------------------------------------- *)
(* Next-state relation: any enabled action of any process *)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

(* ------------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

(* ------------------------------------------------------------------------- *)
(* Safety invariant: type correctness *)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

(* ------------------------------------------------------------------------- *)
(* Optional: define the name of the main invariant as required by the cfg *)
THEOREM SpecImpliesTypeOK == Spec => []TypeOK

====
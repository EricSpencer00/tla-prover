---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants (instantiated in the .cfg)
-----------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (including Alive messages)

(*-----------------------------------------------------------------
  Derived sets
-----------------------------------------------------------------*)
AliveMsg == {"Alive"}  \* We model a single type of alive message

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    suspicion,    \* [p \in Proc -> SUBSET Proc], set of processes p suspects
    timeout,      \* [p \in Proc -> [q \in Proc -> Nat]], timeout interval for each pair
    lastHeard,    \* [p \in Proc -> [q \in Proc -> Nat]], ticks since p last heard from q
    clock,        \* [p \in Proc -> Nat], local logical clock for each process
    outbox        \* [p \in Proc -> SUBSET Messages], messages p intends to send

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
ProcPairs == { [sender : p, receiver : q] : p \in Proc /\ q \in Proc /\ p # q }

\* A process p sends an alive message to every other process
SendAlive(p) == 
    { [type |-> "Alive", sender |-> p, receiver |-> q, payload |-> {}] :
        q \in Proc /\ q # p }

\* Increment clock for process p, wrapping to zero when exceeding the max
ClockInc(p) == 
    IF clock[p] + 1 > MaxClock() THEN 0 ELSE clock[p] + 1

\* The maximum relevant clock bound for a process
MaxClock() == 
    Max({SendPoint, PredictPoint} \cup { timeout[p][q] : p \in Proc, q \in Proc, p # q })

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Process actions
-----------------------------------------------------------------*)
SendAliveAction(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox'   = [outbox EXCEPT ![p] = SendAlive(p)]
    /\ clock'    = [clock EXCEPT ![p] = ClockInc(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q # p THEN lastHeard[p][q] + 1 ELSE @ 
                        FOR q \in Proc]

PredictAction(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                        suspicion[p] \cup 
                        { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] }]
    /\ clock'    = [clock EXCEPT ![p] = ClockInc(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q # p THEN lastHeard[p][q] + 1 ELSE @ 
                        FOR q \in Proc]

ReceiveAction(p) ==
    /\ UNCHANGED clock[p]  \* Receive does not change the local clock directly
    /\ \E msgs \in outbox :
        /\ \A m \in msgs :
            /\ m.type = "Alive"
            /\ m.receiver = p
        /\ outbox'   = [outbox EXCEPT ![p] = {}]   \* clear outbox after reception
        /\ suspicion' = [suspicion EXCEPT ![p][senderOf(m)] = 
                            suspicion[p] \ { senderOf(m) } 
                         FOR m \in msgs]
        /\ lastHeard' = [lastHeard EXCEPT ![p][senderOf(m)] = 0 
                         FOR m \in msgs]
        /\ timeout'   = [timeout EXCEPT 
                            ![p][senderOf(m)] = 
                                IF senderOf(m) \in suspicion[p] 
                                THEN timeout[p][senderOf(m)] + 1 
                                ELSE @ 
                        FOR m \in msgs]

\* Helper to extract sender from a message
senderOf(m) == m.sender

\* If no other action is enabled, we allow stuttering
Stutter(p) ==
    /\ UNCHANGED <<suspicion, timeout, lastHeard, clock, outbox>>

ProcessStep(p) ==
    \/ SendAliveAction(p)
    \/ PredictAction(p)
    \/ ReceiveAction(p)
    \/ Stutter(p)

Next ==
    \E p \in Proc : ProcessStep(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

(*-----------------------------------------------------------------
  Type invariant (the one required by the .cfg)
-----------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

=============================================================================
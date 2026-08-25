---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

(*-----------------------------------------------------------------
   Constants (to be supplied by the configuration)
-----------------------------------------------------------------*)
CONSTANTS
    Proc,          \* The set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Interval at which a process sends alive messages
    PredictPoint,  \* Interval at which a process makes predictions
    Messages       \* Set of all possible messages (used by the environment)

(*-----------------------------------------------------------------
   Variables
-----------------------------------------------------------------*)
VARIABLES
    clock,         \* [p \in Proc -> Nat]        local logical clock of each process
    timeout,       \* [p \in Proc -> [q \in Proc -> Nat]]  timeout intervals
    lastHeard,     \* [p \in Proc -> [q \in Proc -> Nat]]  ticks since last alive from q
    suspicion,     \* [p \in Proc -> SUBSET Proc]          suspected processes
    outbox         \* [p \in Proc -> SUBSET Message]       messages a process wants to send

(*-----------------------------------------------------------------
   Message definition (alive only for this spec)
-----------------------------------------------------------------*)
Message == [type : {"alive"}, src : Proc, dst : Proc]

(*-----------------------------------------------------------------
   Helper definitions
-----------------------------------------------------------------*)
SendEnabled(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

PredictEnabled(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

MaxClock ==
    Max({SendPoint, PredictPoint} \cup
        { timeout[p][q] : p \in Proc, q \in Proc })

IncrementCounters(p, lh, to) ==
    [p1 \in Proc |-> 
        [q \in Proc |-> 
            IF p1 = p /\ q # p /\ lh[p][q] < to[p][q] 
               THEN lh[p][q] + 1 
               ELSE lh[p1][q]]]

(*-----------------------------------------------------------------
   Initial state
-----------------------------------------------------------------*)
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
   Send action
-----------------------------------------------------------------*)
Send(p) ==
    LET msgs == { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} } IN
    /\ SendEnabled(p)
    /\ outbox' = [outbox EXCEPT ![p] = msgs]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ timeout' = timeout
    /\ lastHeard' = IncrementCounters(p, lastHeard, timeout)
    /\ UNCHANGED <<suspicion>>

(*-----------------------------------------------------------------
   Predict action
-----------------------------------------------------------------*)
Predict(p) ==
    /\ PredictEnabled(p)
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ timeout' = timeout
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          suspicion[p] \cup 
          { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ lastHeard' = IncrementCounters(p, lastHeard, timeout)
    /\ outbox' = outbox
    /\ UNCHANGED <<>>

(*-----------------------------------------------------------------
   Receive action (environment delivers an arbitrary alive message)
-----------------------------------------------------------------*)
Receive(p) ==
    \E m \in Messages :
        /\ m.type = "alive"
        /\ m.dst = p
        /\ LET q == m.src IN
           /\ clock' = [clock EXCEPT ![p] = 
                 IF clock[p] + 1 > MaxClock THEN 0 ELSE @ + 1]
           /\ outbox' = outbox
           /\ timeout' = 
                 IF q \in suspicion[p] 
                    THEN [timeout EXCEPT ![p][q] = @ + 1] 
                    ELSE timeout
           /\ lastHeard' = 
                 [lastHeard EXCEPT ![p][q] = 0]
           /\ suspicion' = 
                 [suspicion EXCEPT ![p] = suspicion[p] \ {q}]

(*-----------------------------------------------------------------
   Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(*-----------------------------------------------------------------
   Specification
-----------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<clock, timeout, lastHeard, suspicion, outbox>>

(*-----------------------------------------------------------------
   Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Message]

=============================================================================
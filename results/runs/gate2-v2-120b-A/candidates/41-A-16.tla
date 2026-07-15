---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (must be instantiated in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (> 0)
    SendPoint,     \* Positive send interval
    PredictPoint,  \* Positive predict interval, not a multiple of SendPoint
    Messages       \* Set of possible messages (should contain at least "Alive")

(*--------------------------------------------------------------------
  Type definitions
--------------------------------------------------------------------*)
Message == {"Alive"}

ProcessAliveSet(p) == { "Alive" } \cup { "" } \* placeholder for extensions

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    suspicion,      \* [process -> SUBSET Proc]   set of processes each process suspects
  , timeout,        \* [process -> [proc -> Nat]] timeout intervals
  , lastHeard,      \* [process -> [proc -> Nat]] ticks since last alive received
  , clock,          \* [process -> Nat]           local clock
  , outMsgs         \* [process -> SUBSET Messages] outgoing message set

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
AllProcesses == Proc

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outMsgs   = [p \in Proc |-> {}]

IsMultiple(x, y) == x % y = 0

SendAlive(p) ==
    /\ \E t \in Nat :
        /\ clock[p] = t
        /\ IsMultiple(t, SendPoint) /\ ~IsMultiple(t, PredictPoint)
    /\ outMsgs' = [outMsgs EXCEPT ![p] = { "Alive" } \/ outMsgs[p]]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
          [q \in Proc |-> 
                IF timeout[p][q] = 0 THEN lastHeard[p][q] 
                ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ \E t \in Nat :
        /\ clock[p] = t
        /\ IsMultiple(t, PredictPoint) /\ ~IsMultiple(t, SendPoint)
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          suspicion[p] \cup { q \in Proc : 
                /\ q # p
                /\ lastHeard[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
          [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED <<outMsgs, timeout>>

Receive(p) ==
    /\ \A q \in Proc :
          (q # p) => 
            IF "Alive" \in outMsgs[q] THEN 
                lastHeard[p]'[q] = 0 /\ 
                suspicion[p]' = suspicion[p] \ { q } /\ 
                timeout[p]'[q] = timeout[p][q] + 
                    (IF q \in suspicion[p] THEN 1 ELSE 0)
            ELSE 
                UNCHANGED <<lastHeard[p], suspicion[p], timeout[p]>>
    /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]
    /\ clock'   = [clock EXCEPT ![p] = 
          IF clock[p] + 1 > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc }) 
          THEN 0 
          ELSE clock[p] + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outMsgs>>

(*--------------------------------------------------------------------
  Type invariant (as required)
--------------------------------------------------------------------*)
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outMsgs   \in [Proc -> SUBSET Messages]

=============================================================================
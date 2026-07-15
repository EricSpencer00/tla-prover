---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

(*--------------------------------------------------------------------
  Constants (to be supplied by the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    Proc          \* Set of process identifiers
  , d0            \* Default timeout interval (positive integer)
  , SendPoint     \* Send interval (positive integer, not a multiple of PredictPoint)
  , PredictPoint  \* Predict interval (positive integer, not a multiple of SendPoint)
  , Messages      \* Set of all possible messages (must include alive messages)

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
Message == {"alive", "other"}  \* Simplified: we only need an "alive" tag

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    suspicion,    \* [p \in Proc -> SUBSET Proc]  – processes p currently suspects
  , timeout,      \* [p \in Proc -> [q \in Proc -> Nat]] – timeout interval p uses for q
  , lastHeard,    \* [p \in Proc -> [q \in Proc -> Nat]] – ticks since p last heard from q
  , clock,        \* [p \in Proc -> Nat]                     – local clock of p
  , outbox        \* [p \in Proc -> SUBSET Messages]        \* messages p wants to send

vars == << suspicion, timeout, lastHeard, clock, outbox >>

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Alive(p,q) == [type |-> "alive", src |-> p, dst |-> q]

\* All processes are considered "other" processes (including self) for the maps,
\* but actions will ignore the self entry where appropriate.
Other(p) == Proc \ {p}

\* Predicate that checks the basic type invariant
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

\* Helper to compute the minimum of the two intervals
MinInterval(p) == IF SendPoint < PredictPoint THEN SendPoint ELSE PredictPoint

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Process actions
--------------------------------------------------------------------*)
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { Alive(p,q) : q \in Other(p) }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q \in Other(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]
                     \* (no change for self)
                     ]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                        suspicion[p] \cup
                        { q \in Other(p) : lastHeard[p][q] > timeout[p][q] }]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q \in Other(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED << timeout, outbox >>

Receive(p) ==
    /\ \A q \in Other(p) :
          (Alive(q,p) \in outbox[q]) => 
            /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {Alive(q,p)}]
            /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
            /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
            /\ IF q \in suspicion[p]
               THEN timeout' = [timeout EXCEPT ![p][q] = timeout[p][q] + 1]
               ELSE timeout' = timeout
            /\ clock' = [clock EXCEPT ![p] = 
                           IF clock[p] + 1 > Max(SendPoint, PredictPoint) \/
                              \E r \in Proc : clock[p] + 1 > timeout[p][r]
                           THEN 0
                           ELSE clock[p] + 1]
    /\ UNCHANGED outbox \ {p}  \* other processes' outboxes stay unchanged

\* The above Receive(p) quantifies over all possible q; to avoid circular
\* definitions we capture the effect of receiving any subset of incoming
\* alive messages in a single step.
ReceiveAll(p) ==
    LET received == { q \in Other(p) : Alive(q,p) \in outbox[q] } IN
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ 
                     { Alive(q,p) : q \in received }]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                        IF q \in received THEN 0 ELSE lastHeard[p][q]]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ received]
    /\ timeout' = [timeout EXCEPT ![p][q] = 
                        IF q \in received /\ q \in suspicion[p] 
                        THEN timeout[p][q] + 1
                        ELSE timeout[p][q]]
    /\ clock' = [clock EXCEPT ![p] = 
                    IF clock[p] + 1 > Max(SendPoint, PredictPoint) \/
                       \E r \in Proc : clock[p] + 1 > timeout[p][r]
                    THEN 0
                    ELSE clock[p] + 1]
    /\ UNCHANGED << suspicion, timeout, lastHeard, clock >> \* will be overridden above

(*--------------------------------------------------------------------
  Global step (chooses one process to act)
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ ReceiveAll(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Invariant required by the cfg file
--------------------------------------------------------------------*)
InvariantInvariant == TypeOK

=============================================================================
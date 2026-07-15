---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

CONSTANTS
    Proc,        \* Set of process identifiers
    d0,          \* Default timeout interval (positive integer)
    SendPoint,   \* Send interval (positive integer)
    PredictPoint,\* Predict interval (positive integer)
    Messages     \* Set of possible message identifiers (e.g., {"alive"})

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllProcs == Proc
Other(p) == { q \in Proc : q # p }

\* Message record (alive message from sender to receiver)
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc]   set of processes p suspects
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] timeout interval p uses for q
    lastHeard,   \* [p \in Proc -> [q \in Proc -> Nat]] ticks since p last heard from q
    clock,       \* [p \in Proc -> Nat] local clock of each process
    outbox,      \* [p \in Proc -> SUBSET Message] messages p intends to send
    inbox        \* [p \in Proc -> SUBSET Message] messages p has received in the current step

\* ----------------------------------------------------------------------
\* State predicate abbreviations
\* ----------------------------------------------------------------------
EnvReset(p) ==
    /\ clock[p] >= SendPoint
    /\ clock[p] >= PredictPoint
    /\ \A q \in Proc : clock[p] >= timeout[p][q]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]
    /\ inbox     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [type |-> "alive", from |-> p, to |-> q] : q \in Other(p) }]
    /\ \A q \in Proc :
          IF q \in Other(p) THEN
              lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
          ELSE
              lastHeard' = lastHeard
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<suspicion, timeout, inbox>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
          { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
    /\ \A q \in Proc :
          lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<outbox, timeout, inbox>>

Receive(p) ==
    /\ \A q \in Proc : (q # p) => ( ( [type |-> "alive", from |-> q, to |-> p] \in inbox[p] )
          => lastHeard[p][q] = 0 )
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { q \in Proc :
          [type |-> "alive", from |-> q, to |-> p] \in inbox[p] }]
    /\ timeout' = [timeout EXCEPT
          ![p][q] = IF q \in suspicion[p] /\ [type |-> "alive", from |-> q, to |-> p] \in inbox[p]
                     THEN @ + 1
                     ELSE @
          | q \in Proc]]
    /\ \A q \in Proc :
          IF q # p THEN
              lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1]
          ELSE
              lastHeard' = lastHeard
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]  \* no new outgoing messages in a pure receive step
    /\ UNCHANGED inbox

ClockReset(p) ==
    /\ EnvReset(p)
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox, inbox>>

ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ ClockReset(p)

Next ==
    \E p \in Proc :
        ProcStep(p)

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]
    /\ inbox     \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox, inbox>>

====
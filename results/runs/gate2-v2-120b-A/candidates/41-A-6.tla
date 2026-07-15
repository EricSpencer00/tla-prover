---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\*----------------------------------------------------------------------
\* Constants (to be supplied by the .cfg)
\*----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of message identifiers (used for structure)

\*----------------------------------------------------------------------
\* Derived sets
\*----------------------------------------------------------------------
OtherProc == { p \in Proc : TRUE }  \* Convenience alias; all processes

\*----------------------------------------------------------------------
\* Types
\*----------------------------------------------------------------------
Message == [from : Proc, to : Proc, type : {"alive"}]

\*----------------------------------------------------------------------
\* Variables
\*----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc] : processes p suspects
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] : adaptive timeout per pair
    lastSeen,    \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since p last heard from q
    clock,       \* [p \in Proc -> Nat] : local clock of each process
    outbox       \* [p \in Proc -> SUBSET Message] : messages p intends to send now

\*----------------------------------------------------------------------
\* Initial state
\*----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastSeen  = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\*----------------------------------------------------------------------
\* Helper definitions
\*----------------------------------------------------------------------
NotSend(p) == clock[p] % SendPoint # 0
NotPredict(p) == clock[p] % PredictPoint # 0

SendAlive(p) ==
    /\ NotPredict(p)                     \* we are not at a predict point
    /\ clock[p] % SendPoint = 0          \* and we are at a send point
    /\ outbox' = [outbox EXCEPT ![p] = { [from |-> p, to |-> q, type |-> "alive"] : q \in Proc } ]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastSeen' = [lastSeen EXCEPT
          ![p][q] = IF timeout[p][q] = clock[p] + 1
                    THEN @ + 1
                    ELSE @
          \* (the description says “increments last‑heard counters for processes it has not yet timed out on”)
          ]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ NotSend(p)                         \* we are not at a send point
    /\ clock[p] % PredictPoint = 0        \* and we are at a predict point
    /\ suspicion' = [suspicion EXCEPT
          ![p] = suspicion[p] \cup
                 { q \in Proc : lastSeen[p][q] > timeout[p][q] } ]
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastSeen' = [lastSeen EXCEPT ![p][q] = @ + 1 \* all counters advance
                    ]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ \E msgs \in outbox : \E m \in msgs :
         /\ m.type = "alive"
         /\ m.to = p
         /\ TRUE
    /\ LET recv == { m \in outbox[p] : m.type = "alive" /\ m.to = p } IN
       /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { m.from : m \in recv }]
    /\ timeout'   = [timeout EXCEPT
          ![p][q] =
            IF \E m \in recv : m.from = q
            THEN @ + 1
            ELSE @ ]
    /\ lastSeen'  = [lastSeen EXCEPT
          ![p][q] = IF \E m \in recv : m.from = q THEN 0 ELSE @ + 1]
    /\ clock'    = [clock EXCEPT ![p] = @ + 1]
    /\ outbox'   = [outbox EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastSeen, clock, outbox>>

ClockReset(p) ==
    /\ clock[p] > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, timeout, lastSeen, outbox>>

\*----------------------------------------------------------------------
\* Per‑process step
\*----------------------------------------------------------------------
ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ ClockReset(p)

\*----------------------------------------------------------------------
\* Next-state relation
\*----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : ProcStep(p)

\*----------------------------------------------------------------------
\* Type correctness invariant (required by the cfg)
\*----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastSeen  \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastSeen, clock, outbox>>

\*----------------------------------------------------------------------
\* Theorems / properties (none required beyond TypeOK)
\*----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====
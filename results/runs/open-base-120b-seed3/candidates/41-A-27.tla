---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: period for sending alive messages
    PredictPoint,  \* Positive integer: period for making predictions
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  (process p's suspicion set)
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] (timeout intervals)
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] (ticks since last alive from q)
    clock,       \* [p \in Proc |-> Nat]               (local clock per process)
    outbox       \* SUBSET Messages                     (messages to be sent)

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
OtherProcs(p) == Proc \ {p}

\* Increment counters for all q \in OtherProcs(p) that have not timed out yet
IncCounters(p, lh) ==
    [q \in Proc |-> IF q = p
                      THEN 0
                      ELSE IF lh[p][q] < timeout[p][q]
                              THEN lh[p][q] + 1
                              ELSE lh[p][q]]

\* Maximum relevant clock bound for process p
MaxClock(p) ==
    LET tset == { timeout[p][q] : q \in OtherProcs(p) } \cup { SendPoint, PredictPoint } IN
    IF tset = {} THEN 0 ELSE Max(tset)

\* Reset clock if it would exceed its bound
NextClock(p, c) ==
    IF c + 1 > MaxClock(p) THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = {}

\* ----------------------------------------------------------------------
\* Actions for a single process p
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = outbox \cup { [type |-> "alive", src |-> p, dst |-> q] : q \in OtherProcs(p) }
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ lastHeard' = [lh EXCEPT ![p] = IncCounters(p, lastHeard)]
    /\ clock'     = [c EXCEPT ![p] = NextClock(p, clock[p])]

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ let newSuspects == { q \in OtherProcs(p) : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [s EXCEPT ![p] = s[p] \cup newSuspects]
    /\ timeout'   = timeout
    /\ lastHeard' = [lh EXCEPT ![p] = IncCounters(p, lastHeard)]
    /\ clock'     = [c EXCEPT ![c] = [p] = NextClock(p, clock[p])]
    /\ outbox'    = outbox

Receive(p) ==
    /\ /\ clock[p] % SendPoint # 0
        /\ clock[p] % PredictPoint # 0
    /\ \E rec \in SUBSET { m \in Messages : m.type = "alive" /\ m.dst = p } :
        /\ outbox' = outbox
        /\ clock'   = [c EXCEPT ![p] = NextClock(p, clock[p])]
        /\ suspicion' = [s EXCEPT ![p] = 
                            s[p] \ { m.src : m \in rec } ]
        /\ timeout' = [t EXCEPT ![p][q] =
                         IF \E m \in rec : m.src = q /\ q \in s[p]
                            THEN t[p][q] + 1
                            ELSE t[p][q] ]
        /\ lastHeard' = [lh EXCEPT ![p] = 
                           [q \in Proc |-> IF q \in { m.src : m \in rec }
                                            THEN 0
                                            ELSE IF q = p THEN 0
                                            ELSE lh[p][q] + 1 ]]
    /\ UNCHANGED << suspicion, timeout, lastHeard, clock, outbox >> \* for other processes (handled by existential quantification)

\* ----------------------------------------------------------------------
\* Global Next action (any process may take a step)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : \/ SendAlive(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \subseteq Messages

\* ----------------------------------------------------------------------
\* Required identifiers for the .cfg file
\* ----------------------------------------------------------------------
Init == Init          \* (lower‑case name required by the cfg)
Next == Next          \* (lower‑case name required by the cfg)

INIT == Init
NEXT == Next
INVARIANTS == TypeOK
PROPERTIES == TRUE

====
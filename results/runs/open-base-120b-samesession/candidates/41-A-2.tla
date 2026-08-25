---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,        \* Set of process identifiers
    d0,          \* Default timeout interval (positive integer)
    SendPoint,   \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,\* Predict interval (positive integer, not a multiple of SendPoint)
    Messages     \* Set of possible messages

\* ----------------------------------------------------------------------
\* Message definition (alive messages)
Message == [type : {"Alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   – processes p currently suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] – adaptive timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]                – local clock of p
    msgs         \* SUBSET Messages                       – messages in transit

vars == <<suspicion, timeout, lastHeard, clock, msgs>>

\* ----------------------------------------------------------------------
\* Helper definitions
AllProcExcept(p) == Proc \ {p}

\* Increment last‑heard counters for all q that have not yet timed out
IncLastHeard(p, lh, to) ==
    [q \in Proc |-> IF lh[p][q] < to[p][q] THEN lh[p][q] + 1 ELSE lh[p][q]]

\* Compute the maximal relevant bound for the clock of p
MaxBound(p) ==
    LET tmax == Max({ timeout[p][q] : q \in Proc })
    IN  Max({SendPoint, PredictPoint, tmax})

\* Update the local clock of p respecting the reset rule
UpdateClock(p, c, to) ==
    IF c[p] > MaxBound(p) THEN 0 ELSE c[p] + 1

\* ----------------------------------------------------------------------
\* Initial predicate (lower‑case Init as required by the .cfg)
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ msgs      = {}

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ msgs      \in SUBSET Messages

\* ----------------------------------------------------------------------
\* Actions for a single process p

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \* create alive messages for every other process
       msgs' = msgs \cup {
                [type |-> "Alive", from |-> p, to |-> q] :
                q \in AllProcExcept(p)
             }
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLastHeard(p, lastHeard, timeout)]
    /\ clock'     = [clock EXCEPT ![p] = UpdateClock(p, clock, timeout)]
    /\ UNCHANGED <<suspicion, timeout, lastHeard, clock, msgs>> \* other processes unchanged

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ \* add to suspicion any q whose counter exceeds its timeout
       newSuspects == { q \in AllProcExcept(p) :
                         lastHeard[p][q] > timeout[p][q] }
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
    /\ timeout'   = timeout
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLastHeard(p, lastHeard, timeout)]
    /\ clock'     = [clock EXCEPT ![p] = UpdateClock(p, clock, timeout)]
    /\ msgs' = msgs
    /\ UNCHANGED <<suspicion, timeout, lastHeard, clock, msgs>> \* other processes unchanged

Receive(p) ==
    /\ \* this action is taken when neither send nor predict fires
       /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
       /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ let
          incoming == { m \in msgs : m.to = p }
          senders  == { m.from : m \in incoming }
       in
       /\ \* Reset counters and clear suspicion for each sender
          suspicion' = [suspicion EXCEPT ![p] =
                         suspicion[p] \ (\* remove all senders *\) senders]
          timeout'   = [timeout EXCEPT
                         ![p] = [q \in Proc |-> IF q \in senders /\ q \in suspicion[p]
                                            THEN timeout[p][q] + 1
                                            ELSE timeout[p][q]]]
          lastHeard' = [lastHeard EXCEPT
                         ![p] = [q \in Proc |-> IF q \in senders THEN 0
                                                ELSE IncLastHeard(p, lastHeard, timeout)[q]]]
          clock'     = [clock EXCEPT ![p] = UpdateClock(p, clock, timeout)]
          msgs'      = msgs \ incoming
    /\ UNCHANGED <<suspicion, timeout, lastHeard, clock, msgs>> \* other processes unchanged

\* ----------------------------------------------------------------------
\* Interleaving of actions: one process makes a step at a time
Action(p) == SendAlive(p) \/ Predict(p) \/ Receive(p)

NEXT ==
    \E p \in Proc : Action(p)

\* ----------------------------------------------------------------------
\* Specification
SPECIFICATION == Init /\ [][NEXT]_vars

\* ----------------------------------------------------------------------
\* Required names for the configuration file
INIT == Init
INVARIANTS == TypeOK
PROPERTIES == TRUE

====
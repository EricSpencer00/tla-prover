---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,          \* The set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Interval at which processes send alive messages
    PredictPoint,  \* Interval at which processes make predictions
    Messages       \* The set of all possible messages

\* ----------------------------------------------------------------------
\* ASSUMPTIONS on the constants
\* ----------------------------------------------------------------------
ASSUME SendPoint > 0
ASSUME PredictPoint > 0
\* Send and predict intervals never coincide (not multiples of each other)
ASSUME SendPoint % PredictPoint # 0
ASSUME PredictPoint % SendPoint # 0
ASSUME d0 > 0

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    clock,        \* [p \in Proc |-> Nat]   local clock of each process
    suspicion,    \* [p \in Proc |-> SUBSET Proc]   suspicion set of each process
    timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]]   adaptive timeout intervals
    lastHeard,    \* [p \in Proc |-> [q \in Proc |-> Nat]]   ticks since last alive from q
    out           \* [p \in Proc |-> SUBSET Messages]        outgoing messages

vars == << clock, suspicion, timeout, lastHeard, out >>

\* ----------------------------------------------------------------------
\* MESSAGE CONSTRUCTION
\* ----------------------------------------------------------------------
ALIVE(p,q) == [type |-> "alive", src |-> p, dst |-> q]

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* HELPERS
\* ----------------------------------------------------------------------
\* Maximum of a finite non‑empty set of naturals
MaxNat(S) == IF S = {} THEN 0 ELSE Max(S)

\* For a given process p, the greatest value among its timeout entries,
\* together with the two global intervals.
MaxAll(p) == MaxNat({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })

\* Increment the last‑heard counters for all q that have not yet timed out.
IncCounters(p, lh) ==
    [q \in Proc |-> IF q # p /\ lh[q] < timeout[p][q] THEN lh[q] + 1 ELSE lh[q]]

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { ALIVE(p,q) : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(p, lastHeard[p])]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ let newSus == { q \in Proc :
                         q # p /\ lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncCounters(p, lastHeard[p])]
    /\ UNCHANGED << out, timeout >>

\* Receive action models the effect of receiving an arbitrary subset of
\* alive messages from other processes.
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \* nondeterministically choose the set of senders whose alive message is received
       recvSet \in SUBSET (Proc \ {p})
    /\ \* Update last‑heard counters: reset to 0 for senders, otherwise increment
       lastHeard' = [lastHeard EXCEPT
                       ![p][q] = IF q \in recvSet THEN 0
                                 ELSE IF lastHeard[p][q] < timeout[p][q] THEN @ + 1
                                 ELSE @
                     FOR q \in Proc]
    /\ \* Remove any recovered processes from the suspicion set
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ recvSet]
    /\ \* If a suspected process is heard from, increase its timeout by 1
       timeout' = [timeout EXCEPT
                     ![p][q] = IF q \in recvSet /\ q \in suspicion[p] THEN @ + 1 ELSE @
                   FOR q \in Proc]
    /\ \* Advance (and possibly wrap) the local clock
       clock' = [clock EXCEPT ![p] =
                  IF clock[p] + 1 > MaxAll(p) THEN 0 ELSE @ + 1]
    /\ UNCHANGED out

\* ----------------------------------------------------------------------
\* COMBINED ACTION FOR ONE PROCESS
\* ----------------------------------------------------------------------
ProcAction(p) == Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION (any single process may take a step)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc: ProcAction(p)

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* TYPE INVARIANT
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* REQUIRED NAMES FOR THE .cfg FILE
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====
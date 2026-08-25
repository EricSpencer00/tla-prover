---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Interval for sending alive messages (positive integer)
    PredictPoint,  \* Interval for making predictions (positive integer)
    Messages       \* Superset of all possible messages (used in TypeOK)

\* ----------------------------------------------------------------------
\* Message definition (alive messages only)
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    Suspicions,    \* [p \in Proc |-> SUBSET Proc]  -- suspicion set of each process
    Timeouts,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout for each pair
    LastHeard,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    Clock,         \* [p \in Proc |-> Nat]                     -- local clock of each process
    Outgoing       \* [p \in Proc |-> SUBSET Message]          -- messages to be sent this step

\* ----------------------------------------------------------------------
\* Helper definitions
IsSend(p) == 
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint # 0

IsPredict(p) == 
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint # 0

MaxTimeout(p) == 
    Max({SendPoint, PredictPoint} \cup {Timeouts[p][q] : q \in Proc})

ResetClock(p, v) == 
    IF v >= MaxTimeout(p) THEN 0 ELSE v

IncIfNotTimedOut(p, lh) == 
    [q \in Proc |-> 
        IF lh[p][q] < Timeouts[p][q] THEN lh[p][q] + 1 ELSE lh[p][q]]

IncAll(p, lh) == 
    [q \in Proc |-> lh[p][q] + 1]

\* ----------------------------------------------------------------------
\* Initial predicate
Init ==
    /\ Suspicions = [p \in Proc |-> {}]
    /\ Timeouts   = [p \in Proc |-> [q \in Proc |-> 
                         IF p = q THEN 0 ELSE d0]]
    /\ LastHeard  = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock      = [p \in Proc |-> 0]
    /\ Outgoing   = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Action: Send alive messages
Send(p) ==
    /\ IsSend(p)
    /\ Outgoing' = [Outgoing EXCEPT ![p] = 
          { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} }]
    /\ Suspicions' = Suspicions
    /\ Timeouts'   = Timeouts
    /\ LastHeard'  = [LastHeard EXCEPT ![p] = IncIfNotTimedOut(p, LastHeard)]
    /\ Clock'      = [Clock EXCEPT ![p] = ResetClock(p, Clock[p] + 1)]
    /\ UNCHANGED << Suspicions, Timeouts, LastHeard, Clock >>
    \* (Only the components listed above change; others stay the same)

\* ----------------------------------------------------------------------
\* Action: Make predictions (update suspicion set)
Predict(p) ==
    /\ IsPredict(p)
    /\ let NewSus == Suspicions[p] \cup 
          { q \in Proc \ {p} : LastHeard[p][q] > Timeouts[p][q] } 
       in
       Suspicions' = [Suspicions EXCEPT ![p] = NewSus]
    /\ Timeouts'   = Timeouts
    /\ LastHeard'  = [LastHeard EXCEPT ![p] = IncAll(p, LastHeard)]
    /\ Clock'      = [Clock EXCEPT ![p] = ResetClock(p, Clock[p] + 1)]
    /\ Outgoing'   = Outgoing
    /\ UNCHANGED << Suspicions, Timeouts, LastHeard, Clock, Outgoing >>

\* ----------------------------------------------------------------------
\* Action: Receive messages (nondeterministic set of alive messages)
Receive(p) ==
    /\ ~IsSend(p) /\ ~IsPredict(p)
    /\ \E RecSet \in SUBSET Proc :
         /\ (* RecSet is the set of processes from which p receives an alive message this step *)
         (* No further constraints on RecSet; the environment supplies the actual messages *)
         LET NewLH == [q \in Proc |-> 
                         IF q \in RecSet THEN 0 
                         ELSE LastHeard[p][q] + 1]
         IN
         LastHeard' = [LastHeard EXCEPT ![p] = NewLH]
    /\ Outgoing' = Outgoing
    /\ Suspicions' = [Suspicions EXCEPT ![p] = Suspicions[p] \ RecSet]
    /\ Timeouts' = [Timeouts EXCEPT 
                     ![p][q] = 
                       IF q \in RecSet /\ q \in Suspicions[p] 
                       THEN Timeouts[p][q] + 1 
                       ELSE Timeouts[p][q] 
                   ]
    /\ Clock' = [Clock EXCEPT ![p] = ResetClock(p, Clock[p] + 1)]
    /\ UNCHANGED << Suspicions, Timeouts, LastHeard, Clock, Outgoing >>

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ Suspicions \in [Proc -> SUBSET Proc]
    /\ Timeouts   \in [Proc -> [Proc -> Nat]]
    /\ LastHeard  \in [Proc -> [Proc -> Nat]]
    /\ Clock      \in [Proc -> Nat]
    /\ Outgoing   \in [Proc -> SUBSET Message]
    /\ Outgoing \subseteq Messages

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Suspicions, Timeouts, LastHeard, Clock, Outgoing>>

\* ----------------------------------------------------------------------
\* Exported identifiers
INVARIANTS == TypeOK
\* No explicit liveness properties are required

====
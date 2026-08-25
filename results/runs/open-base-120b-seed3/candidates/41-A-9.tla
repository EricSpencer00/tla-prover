---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Message definition (alive messages)
AliveMessage(p, q) == [type |-> "Alive", src |-> p, dst |-> q]

\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    Suspect,   \* [p \in Proc |-> SUBSET Proc]   -- suspicion set of each process
    Timeout,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout interval per pair
    Last,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last heard
    Clock,     \* [p \in Proc |-> Nat]                    -- local clock per process
    Out        \* [p \in Proc |-> SUBSET Messages]        -- outgoing messages

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ Last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock   = [p \in Proc |-> 0]
    /\ Out     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper predicates for clock multiples
IsSend(p) ==
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint # 0

IsPredict(p) ==
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint # 0

IsReceive(p) ==
    /\ ~IsSend(p)
    /\ ~IsPredict(p)

\* ----------------------------------------------------------------------
\* Send action for process p
Send(p) ==
    /\ IsSend(p)
    /\ Out' = [Out EXCEPT ![p] = { AliveMessage(p, q) : q \in Proc \ {p} }]
    /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ Suspect' = Suspect
    /\ Timeout' = Timeout
    /\ Last' = [Last EXCEPT ![p][q] = Last[p][q] + 1
                         \* increment all counters (simplified) 
                         \* for q \in Proc \ {p}
               | q \in Proc \ {p}]
    /\ UNCHANGED <<Suspect, Timeout>>

\* ----------------------------------------------------------------------
\* Predict action for process p
Predict(p) ==
    /\ IsPredict(p)
    /\ let newSus == Suspect[p] \cup
                     { q \in Proc \ {p} : Last[p][q] > Timeout[p][q] } in
       Suspect' = [Suspect EXCEPT ![p] = newSus]
    /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ Last' = [Last EXCEPT ![p][q] = Last[p][q] + 1
                         | q \in Proc \ {p}]
    /\ Timeout' = Timeout
    /\ Out' = Out
    /\ UNCHANGED <<Suspect, Timeout, Out>>

\* ----------------------------------------------------------------------
\* Receive action for process p
Receive(p) ==
    /\ IsReceive(p)
    /\ \E R \subseteq Proc \ {p} :
         /\ (* R is the set of sources from which p receives an alive message *)
            Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \ R]
         /\ Timeout' = [Timeout EXCEPT
                           ![p][s] = IF s \in Suspect[p] THEN Timeout[p][s] + 1 ELSE Timeout[p][s]
                           | s \in R]
         /\ Last' = [Last EXCEPT
                       ![p][q] = IF q \in R THEN 0 ELSE Last[p][q] + 1
                       | q \in Proc \ {p}]
         /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
         /\ Out' = Out
         /\ UNCHANGED <<Suspect, Timeout, Out>>

\* ----------------------------------------------------------------------
\* A single process step (interleaving semantics)
ProcessStep(p) == \/ Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Next-state relation (any process may take a step)
Next == \E p \in Proc : ProcessStep(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Suspect, Timeout, Last, Clock, Out>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ Last    \in [Proc -> [Proc -> Nat]]
    /\ Clock   \in [Proc -> Nat]
    /\ Out     \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Exported identifiers
Init == Init
Next == Next
TypeOK == TypeOK

====
---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (Nat)
    SendPoint,     \* Set of clock values at which a process sends alive messages
    PredictPoint,  \* Set of clock values at which a process makes predictions
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Message definition (alive messages only)
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspect,   \* [p \in Proc |-> SUBSET Proc]   : current suspicion set of each process
    timeout,   \* [p \in Proc |-> [q \in Proc |-> Nat]] : adaptive timeout intervals
    last,      \* [p \in Proc |-> [q \in Proc |-> Nat]] : ticks since last alive from q
    clock,     \* [p \in Proc |-> Nat]                 : local clock of each process
    outgoing   \* [p \in Proc |-> SUBSET Messages]    : messages a process wants to send

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock   = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
SendSet(p) == { m \in Messages :
                 m.type = "alive" /\ m.from = p /\ m.to \in Proc \ {p} }

ReceivedFrom(p, R) == { m.from : m \in R }

\* ----------------------------------------------------------------------
\* Action: Send alive messages
Send(p) ==
    /\ clock[p] \in SendPoint
    /\ clock[p] \notin PredictPoint
    /\ outgoing' = [outgoing EXCEPT ![p] = SendSet(p)]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'     = [last EXCEPT ![p] = [last[p] EXCEPT ![q] = @ + 1]]
    /\ UNCHANGED << suspect, timeout >>

\* ----------------------------------------------------------------------
\* Action: Make predictions (update suspicion set)
Predict(p) ==
    /\ clock[p] \in PredictPoint
    /\ clock[p] \notin SendPoint
    /\ suspect' = [suspect EXCEPT
                    ![p] = suspect[p] \cup
                           { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'    = [last EXCEPT ![p] = [last[p] EXCEPT ![q] = @ + 1]]
    /\ UNCHANGED << timeout, outgoing >>

\* ----------------------------------------------------------------------
\* Action: Receive incoming alive messages (possibly none)
Receive(p) ==
    /\ clock[p] \notin SendPoint
    /\ clock[p] \notin PredictPoint
    \* Choose a (possibly empty) set of alive messages addressed to p
    \* The controller is responsible for populating this set.
    \* Here we existentially quantify it.
    \E R \in SUBSET Messages :
        /\ \A m \in R : m.type = "alive" /\ m.to = p
        /\ LET rf == ReceivedFrom(p, R) IN
           /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
           /\ last'    = [last EXCEPT
                           ![p] = [last[p] EXCEPT
                                    ![q \in rf] = 0
                                    ![q \in Proc \ rf] = @ + 1]]
           /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ rf]
           /\ timeout' = [timeout EXCEPT
                           ![p] = [timeout[p] EXCEPT
                                    ![q \in (rf \cap suspect[p])] = @ + 1]]
           /\ UNCHANGED << outgoing >>

\* ----------------------------------------------------------------------
\* Next-state relation: one process takes one of the three actions
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clock   \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<suspect, timeout, last, clock, outgoing>>

\* ----------------------------------------------------------------------
\* Invariant to be checked by TLC
INVARIANT TypeOK

====
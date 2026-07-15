---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N, \* total number of processes
    T, \* maximum number of Byzantine faults tolerated
    F  \* actual number of Byzantine processes in a run (0 <= F <= T)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    correct,        \* set of correct processes
    faulty,         \* set of Byzantine processes
    pc,             \* control state of each process
    recv,           \* set of messages received by each process
    sent             \* set of ECHO messages sent by correct processes

\* ----------------------------------------------------------------------
\* Message type
\* ----------------------------------------------------------------------
EchoMsg == [type : "ECHO", sender : Proc]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(mset) == { m.sender : m \in mset }

IsEcho(m) == m.type = "ECHO"

\* Process control locations
Locs == {"InitRecv", "InitNone", "EchoSent", "Accept"}

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> Locs]
    /\ \A p \in Proc :
        IF p \in correct
        THEN
            \/ pc[p] = "InitRecv"
            \/ pc[p] = "InitNone"
        ELSE
            pc[p] = "InitNone"
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in correct
    /\ LET newMsgs == 
            { m \in sent : m \notin recv[p] } 
            \cup
            { [type |-> "ECHO", sender |-> b] : b \in faulty }
       IN 
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitRecv", "InitNone", "EchoSent"}
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ UNCHANGED <<correct, faulty, recv>>

Accept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"InitRecv", "EchoSent", "InitNone"}
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

\* ----------------------------------------------------------------------
\* Combined step for a correct process
\* ----------------------------------------------------------------------
CorrectStep(p) ==
    \/ Receive(p)
    \/ ( /\ pc[p] = "InitRecv"
         /\ SendEcho(p) )
    \/ ( /\ pc[p] \in {"InitNone", "InitRecv"}
         /\ /\ Cardinality(EchoSenders(recv[p])) >= N - 2*T
            /\ Cardinality(EchoSenders(recv[p])) < N - T
         /\ SendEcho(p) )
    \/ ( /\ pc[p] \in {"InitNone", "InitRecv"}
         /\ Cardinality(EchoSenders(recv[p])) >= N - T
         /\ SendEcho(p)
         /\ Accept(p) )
    \/ ( /\ pc[p] = "EchoSent"
         /\ Cardinality(EchoSenders(recv[p])) >= N - T
         /\ Accept(p) )
    \/ ( /\ pc[p] = "InitRecv"
         /\ Accept(p) ) \* immediate accept on init recv

\* No-op action (for stuttering)
Stutter == UNCHANGED <<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in correct : CorrectStep(p)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ faulty = Proc \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Proc -> Locs]
    /\ \A p \in Proc : recv[p] \subseteq { [type |-> "ECHO", sender |-> q] : q \in Proc }
    /\ sent \subseteq { [type |-> "ECHO", sender |-> q] : q \in Proc }

\* Safety property: no acceptance when no correct process received INIT
NoAcceptIfNoInit ==
    ( \A p \in correct : pc[p] # "InitRecv" ) => ( \A p \in correct : pc[p] # "Accept" )

FCConstraints == NoAcceptIfNoInit

\* ----------------------------------------------------------------------
\* LTL properties (expressed as state formulas for TLC)
\* ----------------------------------------------------------------------
CorrLtl == []( \A p \in correct : pc[p] = "InitRecv" => <> ( \A q \in correct : pc[q] = "Accept" ) )
RelayLtl == []( ( \E p \in correct : pc[p] = "Accept" ) => <> ( \A q \in correct : pc[q] = "Accept" ) )
UnforgLtl == []( ( \A p \in correct : pc[p] # "InitRecv" ) => [] ( \A p \in correct : pc[p] # "Accept" ) )

====
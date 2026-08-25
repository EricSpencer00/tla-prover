---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, sender : Proc]

AllMsgs == { [type |-> "ECHO", sender |-> p] : p \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    Correct,          \* set of correct processes
    Faulty,           \* set of Byzantine processes
    recv,             \* messages received by each process
    sent,             \* messages sent by correct processes
    initRecv,         \* whether a process initially received INIT
    sentEcho,         \* whether a correct process has already sent ECHO
    accepted          \* whether a correct process has accepted

vars == <<Correct, Faulty, recv, sent, initRecv, sentEcho, accepted>>

\* ----------------------------------------------------------------------
\* Derived quantities
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }
EchoCount(p)   == Cardinality(EchoSenders(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ Cardinality(Correct) = N - F
    /\ initRecv \in [Proc -> BOOLEAN]
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ sentEcho = [p \in Proc |-> FALSE]
    /\ accepted = [p \in Proc |-> FALSE]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ \E newSet \subseteq ((sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty })
                           \ recv[p]) :
         recv' = [recv EXCEPT ![p] = recv[p] \cup newSet]
    /\ UNCHANGED <<Correct, Faulty, sent, initRecv, sentEcho, accepted>>

\* Process steps that may send ECHO and/or accept
ProcessStep(p) ==
    \/ /\ p \in Correct
       /\ initRecv[p] = TRUE
       /\ ~sentEcho[p] /\ ~accepted[p]
       /\ sent'      = sent \cup { [type |-> "ECHO", sender |-> p] }
       /\ sentEcho'  = [sentEcho EXCEPT ![p] = TRUE]
       /\ accepted'  = [accepted EXCEPT ![p] = TRUE]
       /\ UNCHANGED <<Correct, Faulty, recv, initRecv>>
    \/ /\ p \in Correct
       /\ ~sentEcho[p]
       /\ EchoCount(p) >= N - 2*T
       /\ EchoCount(p) <  N - T
       /\ sent'      = sent \cup { [type |-> "ECHO", sender |-> p] }
       /\ sentEcho'  = [sentEcho EXCEPT ![p] = TRUE]
       /\ UNCHANGED <<Correct, Faulty, recv, initRecv, accepted>>
    \/ /\ p \in Correct
       /\ ~sentEcho[p]
       /\ EchoCount(p) >= N - T
       /\ sent'      = sent \cup { [type |-> "ECHO", sender |-> p] }
       /\ sentEcho'  = [sentEcho EXCEPT ![p] = TRUE]
       /\ accepted'  = [accepted EXCEPT ![p] = TRUE]
       /\ UNCHANGED <<Correct, Faulty, recv, initRecv>>
    \/ /\ p \in Correct
       /\ sentEcho[p]
       /\ EchoCount(p) >= N - T
       /\ ~accepted[p]
       /\ accepted' = [accepted EXCEPT ![p] = TRUE]
       /\ UNCHANGED <<Correct, Faulty, recv, sent, initRecv, sentEcho>>

\* Stuttering step
Stutter ==
    UNCHANGED vars

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : ProcessStep(p)
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars
    /\ \A p \in Correct : WF_vars(Receive(p) \/ ProcessStep(p))

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ sent \subseteq AllMsgs
    /\ recv \in [Proc -> SUBSET AllMsgs]
    /\ initRecv \in [Proc -> BOOLEAN]
    /\ sentEcho \in [Proc -> BOOLEAN]
    /\ accepted \in [Proc -> BOOLEAN]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(Correct) = N - F

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
    ( \A p \in Correct : initRecv[p] ) => <> ( \A p \in Correct : accepted[p] )

RelayLtl ==
    ( \E p \in Correct : accepted[p] ) => <> ( \A p \in Correct : accepted[p] )

UnforgLtl ==
    ( \A p \in Correct : ~initRecv[p] ) => [] ( \A p \in Correct : ~accepted[p] )

=============================================================================
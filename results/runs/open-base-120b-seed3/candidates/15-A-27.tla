---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [sender : Proc, type : {"ECHO"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    Correct,          \* set of correct processes
    Faulty,           \* set of Byzantine processes
    pc,               \* control location of each process
    received,         \* messages received by each correct process
    sent              \* set of ECHO messages that have been sent by correct processes

vars == <<Correct, Faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoFrom(p) == { m.sender : m \in received[p] }
EchoCount(p) == Cardinality(EchoFrom(p))

SentBy(p) == [sender |-> p, type |-> "ECHO"]

ByzMessages == { [sender |-> q, type |-> "ECHO"] : q \in Faulty }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \in SUBSET Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc = [p \in Proc |-> 
                IF p \in Correct 
                THEN IF p \in InitSet THEN "Init1" ELSE "Init0"
                ELSE "Faulty"]
    /\ received = [p \in Proc |-> {}]
    /\ sent = {}
    /\ InitSet \subseteq Correct            \* processes that start having received INIT
    /\ UNCHANGED <<InitSet>>               \* InitSet is a hidden helper, not part of vars

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Receive a (possibly empty) set of new messages
Recv(p, new) ==
    /\ p \in Correct
    /\ new \subseteq (sent \cup ByzMessages) \ received[p]
    /\ received' = [received EXCEPT ![p] = @ \cup new]
    /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* Send an ECHO message (broadcast) if not already sent
SendEcho(p) ==
    /\ p \in Correct
    /\ SentBy(p) \notin sent
    /\ \* Conditions under which a correct process may send ECHO
       ( pc[p] = "Init1"
         \/ (pc[p] = "Init0" /\ EchoCount(p) >= N - 2*T) )
    /\ sent' = sent \cup { SentBy(p) }
    /\ UNCHANGED <<Correct, Faulty, pc, received>>

\* Accept the broadcast
Accept(p) ==
    /\ p \in Correct
    /\ pc[p] # "Accepted"
    /\ \* Acceptance conditions
       ( pc[p] = "Init1"
         \/ (pc[p] = "Init0" /\ EchoCount(p) >= N - T)
         \/ (pc[p] = "EchoSent" /\ EchoCount(p) >= N - T) )
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, received, sent>>

\* Update control location after sending ECHO (if not yet marked)
MarkSent(p) ==
    /\ p \in Correct
    /\ SentBy(p) \in sent
    /\ pc[p] = "Init0"
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ UNCHANGED <<Correct, Faulty, received, sent>>

Next ==
    \/ \E p \in Proc : Recv(p, new)
    \/ \E p \in Proc : SendEcho(p)
    \/ \E p \in Proc : MarkSent(p)
    \/ \E p \in Proc : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"Init0","Init1","EchoSent","Accepted","Faulty"}]
    /\ received \in [Proc -> SUBSET Message]
    /\ sent \subseteq { SentBy(p) : p \in Correct }

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
CorrLtl ==
    ( \A p \in Correct : pc[p] = "Init1" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in Correct : pc[p] = "Init0" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

=============================================================================
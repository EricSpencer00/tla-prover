---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, hasInit, sentEcho, accepted, recv, Sent

vars == <<Correct, Faulty, hasInit, sentEcho, accepted, recv, Sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* messages that may be forged by Byzantine processes
ByzantineMsgs == { [type |-> "ECHO", sender |-> b] : b \in Faulty }

\* set of senders of ECHO messages already received by p
EchoSenders(p) == { m.sender : m \in recv[p] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ hasInit \in [Proc -> BOOLEAN]
    /\ sentEcho \in [Proc -> BOOLEAN]
    /\ accepted \in [Proc -> BOOLEAN]
    /\ recv \in [Proc -> SUBSET Message]
    /\ Sent = {}
    /\ \A p \in Proc :
          /\ sentEcho[p] = FALSE
          /\ accepted[p] = FALSE
          /\ recv[p] = {}
    /\ \A p \in Faulty : hasInit[p] = FALSE
    /\ \A p \in Correct : hasInit[p] \in BOOLEAN

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receiving new messages (from correct senders or Byzantine ones)
Receive(p) ==
    /\ p \in Correct
    /\ LET new \in SUBSET (Sent \cup ByzantineMsgs) \ recv[p] IN
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<Correct, Faulty, hasInit, sentEcho, accepted, Sent>>

\* 2. Sending an ECHO message
SendEcho(p) ==
    /\ p \in Correct
    /\ ~sentEcho[p]
    /\ ( hasInit[p]
        \/ Cardinality(EchoSenders(p)) >= N - 2 * T )
    /\ sentEcho' = [sentEcho EXCEPT ![p] = TRUE]
    /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
    /\ UNCHANGED <<Correct, Faulty, hasInit, accepted, recv>>

\* 3. Accepting the broadcast
Accept(p) ==
    /\ p \in Correct
    /\ ~accepted[p]
    /\ ( hasInit[p]
        \/ Cardinality(EchoSenders(p)) >= N - T )
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<Correct, Faulty, hasInit, sentEcho, recv, Sent>>

\* Combined next-step relation
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ hasInit \in [Proc -> BOOLEAN]
    /\ sentEcho \in [Proc -> BOOLEAN]
    /\ accepted \in [Proc -> BOOLEAN]
    /\ recv \in [Proc -> SUBSET Message]
    /\ Sent \subseteq Message

\* ----------------------------------------------------------------------
\* Constraints on constants (derived from the algorithm's assumptions)
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
\* If all correct processes start having received the INIT, eventually they all accept
CorrLtl == ( \A p \in Correct : hasInit[p] ) => <> ( \A p \in Correct : accepted[p] )

\* If any correct process accepts, eventually all correct processes accept
RelayLtl == ( \E p \in Correct : accepted[p] ) => <> ( \A p \in Correct : accepted[p] )

\* Unforgeability: if no correct process starts with INIT, then no correct process ever accepts
UnforgLtl == ( \A p \in Correct : ~hasInit[p] ) => [] ( \A p \in Correct : ~accepted[p] )

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====
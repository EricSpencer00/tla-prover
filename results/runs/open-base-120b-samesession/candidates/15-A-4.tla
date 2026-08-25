---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [sender : Proc, kind : {"ECHO"}]

AllPossibleMsgs == { [sender |-> q, kind |-> "ECHO"] : q \in Proc }

Echos(p) == { m.sender : m \in recv[p] /\ m.kind = "ECHO" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accept"}]
    /\ \A p \in Correct : pc[p] \in {"Init0", "Init1"}
    /\ recv = [p \in Proc |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Receive action (correct process gets new messages)
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ LET newPossible == { m \in AllPossibleMsgs : m \notin recv[p] } IN
       /\ new \subseteq newPossible
       /\ new # {}
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED << Correct, Faulty, pc, sent >>

\* ----------------------------------------------------------------------
\* Protocol steps for a correct process
\* ----------------------------------------------------------------------
Step(p) ==
    \/ /\ pc[p] = "Init1"
       /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED << Correct, Faulty, recv >>
    \/ /\ pc[p] = "Init0"
       /\ Cardinality(Echos(p)) >= N - 2 * T
       /\ Cardinality(Echos(p)) <  N - T
       /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
       /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
       /\ UNCHANGED << Correct, Faulty, recv >>
    \/ /\ pc[p] = "Init0"
       /\ Cardinality(Echos(p)) >= N - T
       /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED << Correct, Faulty, recv >>
    \/ /\ pc[p] = "EchoSent"
       /\ Cardinality(Echos(p)) >= N - T
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED << Correct, Faulty, recv, sent >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : Step(p)

vars == << Correct, Faulty, pc, recv, sent >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accept"}]
    /\ recv \in [Proc -> SUBSET Message]
    /\ sent \subseteq Message
    /\ N > 3 * T
    /\ F <= T
    /\ F >= 0

FCConstraints ==
    Cardinality(Faulty) = F

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == ( \A p \in Correct : pc[p] = "Init1" ) => <> ( \A p \in Correct : pc[p] = "Accept" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accept" ) => <> ( \A p \in Correct : pc[p] = "Accept" )

UnforgLtl == ( \A p \in Correct : pc[p] = "Init0" ) => [] ( \A p \in Correct : pc[p] # "Accept" )

=============================================================================
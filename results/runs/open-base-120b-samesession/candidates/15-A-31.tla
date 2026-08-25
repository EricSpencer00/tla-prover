---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process universe
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, Sent, recv

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllMsgs == Sent \cup { [type |-> "ECHO", from |-> f] : f \in Faulty }

Senders(p) == { m.from : m \in recv[p] }

InitAll   == \A p \in Correct : pc[p] = "InitRec"
InitNone  == \A p \in Correct : pc[p] = "InitNot"
AllAccept == \A p \in Correct : pc[p] = "Accepted"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  \E InitRecvSet \subseteq Proc :
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ Sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ pc = [p \in Proc |-> 
                IF p \in InitRecvSet 
                THEN "InitRec" 
                ELSE "InitNot"]
    /\ InitRecvSet \subseteq Correct

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET new \subseteq AllMsgs \ recv[p] IN
     /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, pc, Sent>>

SendAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitRec"
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitNot"
  /\ Cardinality(Senders(p)) >= N - 2 * T
  /\ Cardinality(Senders(p)) <  N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitNot"
  /\ Cardinality(Senders(p)) >= N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

Accept(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ Cardinality(Senders(p)) >= N - T
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, Sent, recv>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendAndAccept(p)
  \/ \E p \in Correct : SendEcho(p)
  \/ \E p \in Correct : SendEchoAndAccept(p)
  \/ \E p \in Correct : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Correct, Faulty, pc, Sent, recv>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty   = Proc \ Correct
  /\ pc \in [Proc -> {"InitNot", "InitRec", "EchoSent", "Accepted"}]
  /\ Sent \subseteq { [type |-> "ECHO", from |-> p] : p \in Proc }
  /\ \A p \in Proc : recv[p] \subseteq AllMsgs

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
CorrLtl  == [] ( InitAll => <> AllAccept )
RelayLtl == [] ( (\E p \in Correct : pc[p] = "Accepted") => <> AllAccept )
UnforgLtl == [] ( InitNone => [] ( \A p \in Correct : pc[p] # "Accepted") )

=============================================================================
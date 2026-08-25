---- MODULE bcastByz ----
EXTENDS FiniteSets, Naturals

\*--------------------------------------------------------------------
\* CONSTANTS
\*--------------------------------------------------------------------
CONSTANT N, T, F

\*--------------------------------------------------------------------
\* BASIC SETS
\*--------------------------------------------------------------------
Proc == 1..N

PC   == {"NoINIT", "HasINIT", "EchoSent", "Accepted", "Faulty"}

Message == [type : {"ECHO"}, sender : Proc]

\*--------------------------------------------------------------------
\* VARIABLES
\*--------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, Sent, Recv

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
NMinus2T == N - 2 * T
NMinusT  == N - T

DistinctSenders(p) == { m.sender : m \in Recv[p] }

\*--------------------------------------------------------------------
\* INITIAL STATE
\*--------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \E initRcv \subseteq Correct :
        /\ pc = [p \in Proc |-> 
                IF p \in Faulty THEN "Faulty"
                ELSE IF p \in initRcv THEN "HasINIT"
                ELSE "NoINIT"]
  /\ Sent = {}
  /\ Recv = [p \in Proc |-> {}]

\*--------------------------------------------------------------------
\* RECEIVE ACTION (correct process may obtain new messages)
\*--------------------------------------------------------------------
PossibleMsg ==
  Sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty }

Receive(p) ==
  /\ p \in Correct
  /\ \E new \subseteq PossibleMsg \ Recv[p] :
        /\ Recv' = [Recv EXCEPT ![p] = Recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, Sent>>
  \/ UNCHANGED <<Correct, Faulty, pc, Sent, Recv>>

\*--------------------------------------------------------------------
\* SEND ECHO AND POSSIBLE ACCEPTANCE
\*--------------------------------------------------------------------
SendInitAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "HasINIT"
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, Recv>>

SendEchoThresh(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoINIT"
  /\ cnt == Cardinality(DistinctSenders(p))
  /\ cnt >= NMinus2T
  /\ IF cnt >= NMinusT THEN
        /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
     ELSE
        /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED <<Correct, Faulty, Recv>>

SendEchoAfter(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ Cardinality(DistinctSenders(p)) >= NMinusT
  /\ Sent' = Sent
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Correct, Faulty, Recv>>

\*--------------------------------------------------------------------
\* NEXT RELATION
\*--------------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendInitAccept(p)
  \/ \E p \in Correct : SendEchoThresh(p)
  \/ \E p \in Correct : SendEchoAfter(p)

\*--------------------------------------------------------------------
\* SPECIFICATION
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, Sent, Recv>>

\*--------------------------------------------------------------------
\* INVARIANTS
\*--------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PC]
  /\ Sent \subseteq Message
  /\ Recv \in [Proc -> SUBSET Message]
  /\ \A m \in Sent : m.sender \in Correct
  /\ \A p \in Proc :
        Recv[p] \subseteq PossibleMsg

FCConstraints ==
  ( \A p \in Correct : pc[p] # "HasINIT" )
    => ( \A p \in Correct : pc[p] # "Accepted" )

\*--------------------------------------------------------------------
\* PROPERTIES (LTL)
\*--------------------------------------------------------------------
CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "HasINIT" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accepted" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] # "HasINIT" )
        => ( \A p \in Correct : pc[p] # "Accepted" ) )

=============================================================================
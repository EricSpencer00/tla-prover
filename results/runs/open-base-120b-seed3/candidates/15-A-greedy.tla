---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, from : 1..N]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllPossible == sent \cup { [type |-> "ECHO", from |-> f] : f \in Faulty }

EchoSenders(p) == { m.from : m \in recv[p] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  \E C \subseteq 1..N, I \subseteq C :
    /\ Cardinality(C) = N - F
    /\ Correct = C
    /\ Faulty = 1..N \ C
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]
    /\ pc = [p \in 1..N |-> IF p \in I THEN "Init" ELSE "NoInit"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET new == SUBSET (AllPossible) \ recv[p] IN
     recv' = [recv EXCEPT ![p] = recv[p] \cup new]
  /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitAcceptSend(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoNoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - 2*T
  /\ Cardinality(EchoSenders(p)) <  N - T
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Echo"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ sent' = sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptOnly(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, sent, recv>>

Stutter ==
  UNCHANGED <<Correct, Faulty, pc, sent, recv>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : InitAcceptSend(p)
  \/ \E p \in Correct : SendEchoNoAccept(p)
  \/ \E p \in Correct : SendEchoAndAccept(p)
  \/ \E p \in Correct : AcceptOnly(p)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Correct, Faulty, pc, sent, recv>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Faulty = 1..N \ Correct
  /\ Cardinality(Correct) = N - F
  /\ pc \in [1..N -> {"NoInit", "Init", "Echo", "Accept"}]
  /\ sent \subseteq { [type |-> "ECHO", from |-> p] : p \in 1..N }
  /\ recv \in [1..N -> SUBSET (sent \cup { [type |-> "ECHO", from |-> f] : f \in Faulty })]

FCConstraints ==
  /\ F <= T
  /\ N > 3 * T
  /\ T >= 0
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Init" )
        => <> ( \A p \in Correct : pc[p] = "Accept" ) )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accept" )
        => <> ( \A p \in Correct : pc[p] = "Accept" ) )

UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] = "NoInit" )
        => [] ( \A p \in Correct : pc[p] # "Accept" ) )

====
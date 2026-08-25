---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

AllCorrectAccept == \A p \in Correct : pc[p] = "Accept"
AllCorrectInit   == \A p \in Correct : pc[p] = "Init"
AllCorrectNoInit == \A p \in Correct : pc[p] = "NoInit"

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"NoInit", "Init", "Echo", "Accept"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "Init"}
  /\ \A p \in Faulty : pc[p] = "NoInit"
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Receive action (correct process may receive any subset of
\* messages that have been sent by correct processes together with
\* arbitrary ECHO messages from Byzantine processes)
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty } IN
     \E new \subseteq possible :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* ----------------------------------------------------------------------
\* Actions for correct processes
\* ----------------------------------------------------------------------
SendEchoAndAcceptFromInit(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoNoAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ LET es == EchoSenders(p) IN
        /\ Cardinality(es) >= N - 2 * T
        /\ Cardinality(es) <  N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Echo"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ LET es == EchoSenders(p) IN
        Cardinality(es) >= N - T
  /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ LET es == EchoSenders(p) IN
        Cardinality(es) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendEchoAndAcceptFromInit(p)
  \/ \E p \in Correct : SendEchoNoAccept(p)
  \/ \E p \in Correct : SendEchoAndAccept(p)
  \/ \E p \in Correct : AcceptAfterEcho(p)
  \/ UNCHANGED vars

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
  /\ pc \in [Proc -> {"NoInit", "Init", "Echo", "Accept"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "Init", "Echo", "Accept"}
  /\ \A p \in Faulty  : pc[p] = "NoInit"
  /\ sent \subseteq { [type |-> "ECHO", sender |-> q] : q \in Correct }
  /\ recv \in [Proc -> SUBSET { [type |-> "ECHO", sender |-> q] : q \in Proc }]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == (AllCorrectInit) ~> (AllCorrectAccept)

RelayLtl == (\E p \in Correct : pc[p] = "Accept") ~> (AllCorrectAccept)

UnforgLtl == (AllCorrectNoInit) => [] ( \A p \in Correct : pc[p] # "Accept" )

\* ----------------------------------------------------------------------
\* Theorems for model checking (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====
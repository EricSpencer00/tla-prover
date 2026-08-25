---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Basic sets and records
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

EchoFrom(p) == [type |-> "ECHO", sender |-> p]

EchoSenders(p) ==
  { m.sender : m \in recv[p] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"NoInit", "InitReceived", "EchoSent", "Accepted"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "InitReceived"}
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty } IN
       \E newMsgs \subseteq possible \ recv[p] :
         /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
         /\ UNCHANGED <<Correct, Faulty, pc, sent>>

DoSend(p, newPc) ==
  /\ sent' = sent \cup { EchoFrom(p) }
  /\ pc'   = [pc EXCEPT ![p] = newPc]
  /\ UNCHANGED <<Correct, Faulty, recv>>

InitStep(p) ==
  /\ pc[p] = "InitReceived"
  /\ DoSend(p, "Accepted")

SendEchoOnly(p) ==
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - 2 * T
  /\ Cardinality(EchoSenders(p)) <  N - T
  /\ DoSend(p, "EchoSent")

SendEchoAndAccept(p) ==
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ DoSend(p, "Accepted")

SendAcceptAfterEcho(p) ==
  /\ pc[p] = "EchoSent"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ DoSend(p, "Accepted")

Next ==
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : InitStep(p)
  \/ \E p \in Proc : SendEchoOnly(p)
  \/ \E p \in Proc : SendEchoAndAccept(p)
  \/ \E p \in Proc : SendAcceptAfterEcho(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"NoInit", "InitReceived", "EchoSent", "Accepted"}]
  /\ recv \in [Proc -> SUBSET Message]
  /\ sent \in SUBSET Message
  /\ \A m \in sent :
        /\ m.type = "ECHO"
        /\ m.sender \in Correct
  /\ \A p \in Proc :
        \A m \in recv[p] :
          /\ m.type = "ECHO"
          /\ m.sender \in Proc

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  ( \A p \in Correct : pc[p] = "InitReceived" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
  ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

====
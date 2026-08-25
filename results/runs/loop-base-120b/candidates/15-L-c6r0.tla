---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Msg == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, Sent, Rec, pc

vars == << correct, faulty, Sent, Rec, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllByzantineMsgs ==
  { [type |-> "ECHO", sender |-> s] : s \in faulty }

EchoSenders(p) ==
  { m.sender : m \in Rec[p] /\ m.type = "ECHO" }

EchoCount(p) ==
  Cardinality( EchoSenders(p) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ Sent = {}
  /\ Rec = [p \in Proc |-> {}]
  /\ pc \in [Proc -> {"NoInit", "InitRcv", "EchoSent", "Accepted"}]
  /\ \A p \in correct : pc[p] \in {"NoInit", "InitRcv"}
  /\ \A p \in faulty  : pc[p] = "NoInit"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in correct
  /\ LET possible == (Sent \cup AllByzantineMsgs) \ Rec[p] IN
       \E new \subseteq possible :
         Rec' = [Rec EXCEPT ![p] = Rec[p] \cup new]
  /\ UNCHANGED << correct, faulty, Sent, pc >>

SendEchoAndAcceptInit(p) ==
  /\ p \in correct
  /\ pc[p] = "InitRcv"
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << Rec, correct, faulty >>

SendEchoOnly(p) ==
  /\ p \in correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= N - 2 * T
  /\ EchoCount(p) <  N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED << Rec, correct, faulty >>

SendEchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "NoInit"
  /\ EchoCount(p) >= N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << Rec, correct, faulty >>

AcceptOnly(p) ==
  /\ p \in correct
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << Rec, Sent, correct, faulty >>

Next ==
  \E p \in Proc :
       Receive(p)
    \/ SendEchoAndAcceptInit(p)
    \/ SendEchoOnly(p)
    \/ SendEchoAndAccept(p)
    \/ AcceptOnly(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ Cardinality(correct) = N - F
  /\ Sent \subseteq Msg
  /\ Rec \in [Proc -> SUBSET Msg]
  /\ pc \in [Proc -> {"NoInit", "InitRcv", "EchoSent", "Accepted"}]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
AllInit == \A p \in correct : pc[p] = "InitRcv"
NoInit  == \A p \in correct : pc[p] = "NoInit"
AllAccepted == \A p \in correct : pc[p] = "Accepted"
AnyAccepted == \E p \in correct : pc[p] = "Accepted"

CorrLtl == (AllInit) => <> (AllAccepted)

RelayLtl == [] ( AnyAccepted => <> (AllAccepted) )

UnforgLtl == [] ( NoInit => [] ( ~AnyAccepted ) )

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* CONSTANTS: N, T, F   (declared above)
\* SPECIFICATION formula: Spec
\* INVARIANTS: TypeOK, FCConstraints
\* PROPERTIES: CorrLtl, RelayLtl, UnforgLtl
=============================================================================
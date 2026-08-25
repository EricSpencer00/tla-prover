---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO type)
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PossibleMsgs == sent \cup { [type |-> "ECHO", sender |-> f] : f \in Faulty }

Senders(p) == { m.sender : m \in recv[p] }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \A p \in Proc :
        IF p \in Correct THEN pc[p] \in {"Init","NoInit"}
        ELSE pc[p] = "Faulty"
  /\ sent = {}
  /\ \A p \in Proc : recv[p] = {}

\* ----------------------------------------------------------------------
\* Receive action: a correct process may receive any subset of messages
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ \E new \in SUBSET(PossibleMsgs \ recv[p]) :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* ----------------------------------------------------------------------
\* Send ECHO / Accept actions
\* ----------------------------------------------------------------------
SendEcho(p) ==
  \/ /\ pc[p] = "Init"
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ pc[p] = "NoInit"
        /\ LET cnt == Cardinality(Senders(p)) IN
           cnt >= N - 2*T /\ cnt < N - T
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
        /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ pc[p] = "NoInit"
        /\ Cardinality(Senders(p)) >= N - T
        /\ sent' = sent \cup { [type |-> "ECHO", sender |-> p] }
        /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ UNCHANGED <<Correct, Faulty, recv>>
  \/ /\ pc[p] = "EchoSent"
        /\ Cardinality(Senders(p)) >= N - T
        /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
        /\ UNCHANGED <<Correct, Faulty, sent, recv>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendEcho(p)

\* ----------------------------------------------------------------------
\* Specification (with weak fairness on Next)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, sent, recv>> /\ WF_<<Correct, Faulty, pc, sent, recv>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \A p \in Proc : pc[p] \in {"Init","NoInit","EchoSent","Accepted","Faulty"}
  /\ sent \subseteq { [type |-> "ECHO", sender |-> s] : s \in Correct }
  /\ \A p \in Proc : recv[p] \subseteq { [type |-> "ECHO", sender |-> s] : s \in Proc }

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
InitAll == \A p \in Correct : pc[p] = "Init"
InitNone == \A p \in Correct : pc[p] = "NoInit"

AllAccepted == \A p \in Correct : pc[p] = "Accepted"
SomeAccepted == \E p \in Correct : pc[p] = "Accepted"

CorrLtl == InitAll => <> AllAccepted
RelayLtl == SomeAccepted => <> AllAccepted
UnforgLtl == InitNone => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
\* The following names are required by the .cfg file
\* (they must appear exactly with these names)
\*   CONSTANTS: N, T, F
\*   SPECIFICATION: Spec
\*   INVARIANTS: TypeOK, FCConstraints
\*   PROPERTIES: CorrLtl, RelayLtl, UnforgLtl
=============================================================================
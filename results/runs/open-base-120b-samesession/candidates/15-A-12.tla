---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process universe
\* ----------------------------------------------------------------------
Proc == 1..N

MsgType == {"ECHO"}

Message == [sender : Proc, type : MsgType]

AllMsgs == { [sender |-> s, type |-> "ECHO"] : s \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, init, echo, acc, sent, recv

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
EchoReceived(p) == { m \in recv[p] : m.type = "ECHO" }

Senders(set) == { m.sender : m \in set }

CntEcho(p, msgs) == Cardinality( Senders( { m \in msgs : m.type = "ECHO" } ) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ init \in [Proc -> BOOLEAN]          \* may be true or false for each process
  /\ echo = [p \in Proc |-> FALSE]
  /\ acc  = [p \in Proc |-> FALSE]
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Receive and act step for a correct process
\* ----------------------------------------------------------------------
ReceiveAct(p) ==
  /\ p \in correct
  /\ LET newMsgs == SUBSET AllMsgs IN
     LET recvNew == recv[p] \cup newMsgs IN
     LET cnt == Cardinality( Senders( { m \in recvNew : m.type = "ECHO" } ) ) IN
     LET echoNow == echo[p] \/ ( ~echo[p] /\ cnt >= N - 2 * T ) IN
     LET accNow  == acc[p]  \/ init[p] \/ ( cnt >= N - T ) IN
     /\ recv' = [recv EXCEPT ![p] = recvNew]
     /\ echo' = [echo EXCEPT ![p] = echoNow]
     /\ acc'  = [acc  EXCEPT ![p] = accNow]
     /\ sent' = IF echoNow /\ ~echo[p]
                THEN sent \cup { [sender |-> p, type |-> "ECHO"] }
                ELSE sent
     /\ UNCHANGED << correct, faulty, init >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : ReceiveAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<correct, faulty, init, echo, acc, sent, recv>>
  /\ WF_<<correct, faulty, init, echo, acc, sent, recv>>(Next)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ init \in [Proc -> BOOLEAN]
  /\ echo \in [Proc -> BOOLEAN]
  /\ acc  \in [Proc -> BOOLEAN]
  /\ sent \subseteq { [sender |-> p, type |-> "ECHO"] : p \in correct }
  /\ recv \in [Proc -> SUBSET { [sender |-> p, type |-> "ECHO"] : p \in Proc }]

\* ----------------------------------------------------------------------
\* Fault‑configuration constraints
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl ==
  ( \A p \in correct : init[p] ) => <> ( \A p \in correct : acc[p] )

RelayLtl ==
  ( \E p \in correct : acc[p] ) => <> ( \A p \in correct : acc[p] )

UnforgLtl ==
  ( \A p \in correct : ~init[p] ) => [] ( \A p \in correct : ~acc[p] )

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => FCConstraints

====
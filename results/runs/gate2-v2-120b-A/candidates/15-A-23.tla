---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1..N

MsgType == {"ECHO"}

Msg == [snd: Proc, typ: MsgType]

ProcSet == SUBSET Proc

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty,
          pc,          \* control location of each process
          sent,        \* messages sent by correct processes
          recv         \* messages received by each process

\* ----------------------------------------------------------------------
\* Phases for control locations
\* ----------------------------------------------------------------------
Phases == {"InitNo", "InitYes", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
InitVals ==
  CHOOSE cs \in ProcSet :
    Cardinality(cs) = N - F

Init ==
 /\ correct = InitVals
 /\ faulty = Proc \ correct
 /\ sent = {}
 /\ pc = [p \in Proc |-> IF p \in correct THEN "InitNo" ELSE "InitNo"]
 /\ recv = [p \in Proc |-> {}]

InitAllInit ==
  Init /\ 
  \A p \in correct: pc[p] = "InitYes"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoFrom(p) == [snd |-> p, typ |-> "ECHO"]

DistinctSenders(S) == { m.snd : m \in S }

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
 /\ pc[p] \in {"InitNo", "InitYes", "EchoSent", "Accepted"}
 /\ recv' = [recv EXCEPT ![p] = recv[p] \cup (sent \cup { EchoFrom(p) : p \in faulty })]
 /\ UNCHANGED <<correct, faulty, sent, pc>>

BroadcastInit(p) ==
 /\ p \in correct
 /\ pc[p] = "InitYes"
 /\ sent' = sent \cup { EchoFrom(p) }
 /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
 /\ UNCHANGED <<correct, faulty, recv>>

SendEcho(p) ==
 /\ p \in correct
 /\ pc[p] = "InitNo"
 /\ LET echoCount == Cardinality({ m \in recv[p] : m.typ = "ECHO" }) IN
    /\ echoCount >= (N - 2*T)
    /\ echoCount < (N - T)
 /\ sent' = sent \cup { EchoFrom(p) }
 /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
 /\ UNCHANGED <<correct, faulty, recv>>

SendEchoAndAccept(p) ==
 /\ p \in correct
 /\ ( pc[p] = "InitNo" \/ pc[p] = "EchoSent" )
 /\ LET echoCount == Cardinality({ m \in recv[p] : m.typ = "ECHO" }) IN
    /\ echoCount >= (N - T)
 /\ sent' = sent \cup { EchoFrom(p) }
 /\ pc' = [pc EXCEPT ![p] = "Accepted"]
 /\ UNCHANGED <<correct, faulty, recv>>

Accept(p) ==
 /\ p \in correct
 /\ pc[p] = "EchoSent"
 /\ LET echoCount == Cardinality({ m \in recv[p] : m.typ = "ECHO" }) IN
    /\ echoCount >= (N - T)
 /\ pc' = [pc EXCEPT ![p] = "Accepted"]
 /\ UNCHANGED <<correct, faulty, sent, recv>>

Next ==
 \/ \E p \in Proc : Receive(p)
 \/ \E p \in correct : BroadcastInit(p)
 \/ \E p \in correct : SendEcho(p)
 \/ \E p \in correct : SendEchoAndAccept(p)
 \/ \E p \in correct : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<correct, faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
 /\ correct \subseteq Proc
 /\ faulty \subseteq Proc
 /\ correct \cap faulty = {}
 /\ pc \in [Proc -> Phases]
 /\ sent \subseteq Msg
 /\ recv \in [Proc -> SUBSET Msg]
 /\ \A p \in Proc : \A m \in recv[p] : m \in sent \/ (m.snd \in faulty)

FCConstraints == Cardinality(correct) = N - F

\* ----------------------------------------------------------------------
\* Safety Property (Unforgeability) expressed as an invariant
\* ----------------------------------------------------------------------
NoAcceptIfNoInit ==
 /\ \A p \in correct : pc[p] # "InitYes"
 => \A p \in correct : pc[p] # "Accepted"

\* ----------------------------------------------------------------------
\* Liveness Properties (encoded as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == 
  ( \A p \in correct : pc[p] = "InitYes" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" )

UnforgLtl == [] NoAcceptIfNoInit

=============================================================================
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets and derived constants
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [sender : Proc, type : {"ECHO"}]

NMinus2T == N - 2 * T
NMinusT  == N - T

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == << Correct, Faulty, pc, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Control locations for correct processes
PCVals == {"NoInit", "InitRecv", "EchoSent", "Accepted", "Faulty"}

\* The set of ECHO messages that a process p has received
EchoSenders(p) == { m.sender : m \in recv[p] /\ m.type = "ECHO" }

EchoCount(p) == Cardinality(EchoSenders(p))

\* All possible ECHO messages that could be sent by Byzantine processes
ByzMsgs == { [sender |-> f, type |-> "ECHO"] : f \in Faulty }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F
  /\ \A p \in Proc :
        IF p \in Correct THEN
           pc[p] \in {"NoInit", "InitRecv"}
        ELSE
           pc[p] = "Faulty"
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Receive a (possibly empty) set of new messages
Receive(p) ==
  /\ p \in Correct
  /\ LET possible == sent \cup ByzMsgs IN
     \E new \subseteq possible :
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
        /\ UNCHANGED << Correct, Faulty, pc, sent >>

\* 2. Correct process that has the INIT message accepts immediately and sends ECHO
InitRecvAccept(p) ==
  /\ p \in Correct
  /\ pc[p] = "InitRecv"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ UNCHANGED << recv, Correct, Faulty >>

\* 3. Correct process that has not yet sent ECHO receives enough (N-2T) but less than (N-T) ECHOs
SendEchoOnly(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"NoInit", "InitRecv"}    \* has not sent ECHO yet
  /\ EchoCount(p) >= NMinus2T
  /\ EchoCount(p) <  NMinusT
  /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ UNCHANGED << recv, Correct, Faulty >>

\* 4. Correct process that has not yet sent ECHO receives at least (N-T) ECHOs
SendEchoAndAccept(p) ==
  /\ p \in Correct
  /\ pc[p] \in {"NoInit", "InitRecv"}    \* has not sent ECHO yet
  /\ EchoCount(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ UNCHANGED << recv, Correct, Faulty >>

\* 5. Correct process that has already sent ECHO now receives at least (N-T) ECHOs
AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "EchoSent"
  /\ EchoCount(p) >= NMinusT
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << recv, sent, Correct, Faulty >>

\* Combine all possible steps of a correct process
ProcStep(p) == Receive(p) \/ InitRecvAccept(p) \/ SendEchoOnly(p) \/ SendEchoAndAccept(p) \/ AcceptAfterEcho(p)

Next ==
  \E p \in Correct : ProcStep(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PCVals]
  /\ sent \subseteq Message
  /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Correct
  /\ recv \in [Proc -> SUBSET Message]
  /\ \A p \in Proc : \A m \in recv[p] : m.type = "ECHO" /\ m.sender \in Proc

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F

\* ----------------------------------------------------------------------
\* Temporal properties (LTL style)
\* ----------------------------------------------------------------------
AllInitRecv == \A p \in Correct : pc[p] = "InitRecv"
AllNoInit   == \A p \in Correct : pc[p] = "NoInit"
AllAccepted == \A p \in Correct : pc[p] = "Accepted"

CorrLtl   == [] (AllInitRecv => <> AllAccepted)

RelayLtl  == [] ( (\E p \in Correct : pc[p] = "Accepted") => <> AllAccepted )

UnforgLtl == [] (AllNoInit => [] (\A p \in Correct : pc[p] # "Accepted"))

=============================================================================
---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [sender : Proc, type : {"ECHO"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, pc, sent, recv

vars == << correct, faulty, pc, sent, recv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
InitState == {"InitRecv", "InitNone"}
PostState == {"EchoSent", "Accepted"}

EchoSenders(p) == { m.sender : m \in recv[p] }

CountEchoSenders(p) == Cardinality( EchoSenders(p) )

PossibleMsgs(p) ==
    sent \cup { [sender |-> f, type |-> "ECHO"] : f \in faulty }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  \E corrSet \in SUBSET Proc :
    /\ Cardinality(corrSet) = N - F
    /\ correct = corrSet
    /\ faulty = Proc \ correct
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ \E pcInit \in [correct -> InitState] :
         pc = [p \in Proc |-> IF p \in correct THEN pcInit[p] ELSE "InitNone"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Receive a (possibly empty) set of new messages
Receive(p) ==
  /\ p \in correct
  /\ LET newMsgs == 
        { m \in PossibleMsgs(p) : m \notin recv[p] }
     IN \E delta \in SUBSET newMsgs :
        /\ recv' = [recv EXCEPT ![p] = @ \cup delta]
        /\ UNCHANGED << correct, faulty, pc, sent >>

\* Process that started with INIT: immediately send ECHO and accept
InitRecvAct(p) ==
  /\ p \in correct
  /\ pc[p] = "InitRecv"
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << correct, faulty, recv >>

\* Send ECHO after receiving >= N-2T but < N-T distinct ECHOs, without accepting yet
SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "InitNone"
  /\ CountEchoSenders(p) >= N - 2*T
  /\ CountEchoSenders(p) < N - T
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ UNCHANGED << correct, faulty, recv >>

\* Send ECHO and accept after receiving >= N-T distinct ECHOs (and not sent before)
SendEchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "InitNone"
  /\ CountEchoSenders(p) >= N - T
  /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << correct, faulty, recv >>

\* Accept after already having sent ECHO and now receiving >= N-T distinct ECHOs
AcceptAfterEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "EchoSent"
  /\ CountEchoSenders(p) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED << correct, faulty, sent, recv >>

\* The combined step a correct process may take
ProcStep(p) ==
    \/ Receive(p)
    \/ InitRecvAct(p)
    \/ SendEcho(p)
    \/ SendEchoAndAccept(p)
    \/ AcceptAfterEcho(p)

\* Next relation: one correct process makes a step
Next ==
  \E p \in correct : ProcStep(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars( \E p \in correct : ProcStep(p) )

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> InitState \cup PostState]
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* Useful predicates for LTL properties
\* ----------------------------------------------------------------------
AllAccepted == \A p \in correct : pc[p] = "Accepted"

InitAllBroadcast == Init /\ \A p \in correct : pc[p] = "InitRecv"

InitNoBroadcast == Init /\ \A p \in correct : pc[p] = "InitNone"

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == InitAllBroadcast => <> AllAccepted

RelayLtl == [] ( (\E p \in correct : pc[p] = "Accepted") => <> AllAccepted )

UnforgLtl == InitNoBroadcast => [] ( \A p \in correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====
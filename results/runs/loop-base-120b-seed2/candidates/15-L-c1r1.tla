---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N

Msg == [type : {"ECHO"}, from : Proc]

AllMsg == { [type |-> "ECHO", from |-> q] : q \in Proc }

PcVals == {"Init0", "Init1", "EchoSent", "Accepted"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Senders(msgSet) == { m.from : m \in msgSet }

SendNow(p, newRecv) ==
  \/ pc[p] = "Init1"
  \/ (pc[p] = "Init0" /\ Cardinality(Senders(newRecv)) >= N - 2 * T
                                /\ Cardinality(Senders(newRecv)) <  N - T)
  \/ (pc[p] = "Init0" /\ Cardinality(Senders(newRecv)) >= N - T)
  \/ (pc[p] = "EchoSent" /\ Cardinality(Senders(newRecv)) >= N - T)

AcceptNow(p, newRecv) ==
  \/ pc[p] = "Init1"
  \/ (pc[p] = "Init0" /\ Cardinality(Senders(newRecv)) >= N - T)
  \/ (pc[p] = "EchoSent" /\ Cardinality(Senders(newRecv)) >= N - T)

UpdatePC(p, newRecv) ==
  IF AcceptNow(p, newRecv) THEN "Accepted"
  ELSE IF SendNow(p, newRecv) /\ pc[p] = "Init0" THEN "EchoSent"
  ELSE pc[p]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> PcVals]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent = {}
  /\ \A p \in Proc : recv[p] = {}

\* ----------------------------------------------------------------------
\* Per‑process action (receive arbitrary new messages and then act)
\* ----------------------------------------------------------------------
ProcAct(p) ==
  \E newMsgs \in SUBSET SetMinus(AllMsg, recv[p]) :
    LET newRecv == recv[p] \cup newMsgs IN
      /\ recv' = [recv EXCEPT ![p] = newRecv]
      /\ sent' = IF SendNow(p, newRecv) /\ ~([type |-> "ECHO", from |-> p] \in sent)
                 THEN sent \cup { [type |-> "ECHO", from |-> p] }
                 ELSE sent
      /\ pc'   = [pc EXCEPT ![p] = UpdatePC(p, newRecv)]
      /\ UNCHANGED << correct, faulty >>

Next ==
  \/ \E p \in correct : ProcAct(p)

\* ----------------------------------------------------------------------
\* Specification (including weak fairness for each correct process)
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_vars /\ \A p \in correct : WF_vars(ProcAct(p))

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> PcVals]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent \in SUBSET Msg
  /\ \A m \in sent : m.type = "ECHO" /\ m.from \in Proc
  /\ \A p \in Proc : \A m \in recv[p] : m.type = "ECHO" /\ m.from \in Proc

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  [] ( ( \A p \in correct : pc[p] = "Init1" )
       => <> ( \A p \in correct : pc[p] = "Accepted" ) )

RelayLtl ==
  [] ( ( \E p \in correct : pc[p] = "Accepted" )
       => <> ( \A p \in correct : pc[p] = "Accepted" ) )

UnforgLtl ==
  [] ( ( \A p \in correct : pc[p] = "Init0" )
       => ( \A p \in correct : pc[p] # "Accepted" ) )

====
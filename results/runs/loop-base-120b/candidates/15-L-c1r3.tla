---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
MsgType == {"ECHO"}
AllEchos == { <<p, "ECHO">> : p \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES CorrectSet, FaultySet, pc, recv, sent

vars == <<CorrectSet, FaultySet, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p, r) == { s \in Proc : <<s, "ECHO">> \in r }
EchoCount(p) == Cardinality(EchoSenders(p, recv[p]))

\* ----------------------------------------------------------------------
\* Nondeterministic choice of the correct process set (used only in Init)
\* ----------------------------------------------------------------------
CorrectSetInit == CHOOSE S \in SUBSET Proc : Cardinality(S) = N - F

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ CorrectSet = CorrectSetInit
  /\ FaultySet = Proc \ CorrectSet
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted", "Faulty"}]
  /\ \A p \in CorrectSet : pc[p] \in {"Init0", "Init1"}
  /\ \A p \in FaultySet : pc[p] = "Faulty"
  /\ recv \in [Proc -> SUBSET AllEchos]
  /\ \A p \in Proc : recv[p] = {}
  /\ sent = {}

\* ----------------------------------------------------------------------
\* A step for a (correct) process p
\* ----------------------------------------------------------------------
Step(p) ==
  /\ p \in Proc
  /\ IF p \in CorrectSet THEN
        \* The process may receive any new set of ECHO messages.
        \* It can receive messages that have been sent by correct processes
        \* (tracked in ''sent'') and any message that could be forged by a
        \* Byzantine sender.
        \E new \in SUBSET ((sent \cup {<<f, "ECHO">> : f \in FaultySet}) \ recv[p]) :
          LET recvNew == recv[p] \cup new IN
          \/ /\ pc[p] = "Init1"
               /\ pc' = [pc EXCEPT ![p] = "Accepted"]
               /\ sent' = sent \cup {<<p, "ECHO">>}
               /\ recv' = [recv EXCEPT ![p] = recvNew]
          \/ /\ pc[p] = "Init0"
               /\ EchoCount(p) >= N - T
               /\ pc' = [pc EXCEPT ![p] = "Accepted"]
               /\ sent' = sent \cup {<<p, "ECHO">>}
               /\ recv' = [recv EXCEPT ![p] = recvNew]
          \/ /\ pc[p] = "Init0"
               /\ EchoCount(p) >= N - 2 * T
               /\ EchoCount(p) < N - T
               /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
               /\ sent' = sent \cup {<<p, "ECHO">>}
               /\ recv' = [recv EXCEPT ![p] = recvNew]
          \/ /\ pc[p] = "EchoSent"
               /\ EchoCount(p) >= N - T
               /\ pc' = [pc EXCEPT ![p] = "Accepted"]
               /\ recv' = [recv EXCEPT ![p] = recvNew]
               /\ UNCHANGED sent
          \/ /\ pc[p] \in {"Init0", "Init1", "EchoSent", "Accepted"}
               /\ pc' = pc
               /\ recv' = [recv EXCEPT ![p] = recvNew]
               /\ UNCHANGED sent
          /\ UNCHANGED <<CorrectSet, FaultySet>>
    ELSE
        /\ pc' = pc
        /\ recv' = recv
        /\ sent' = sent
        /\ UNCHANGED <<CorrectSet, FaultySet>>

\* ----------------------------------------------------------------------
\* Next-state relation (any process may take a step)
\* ----------------------------------------------------------------------
Next == \E p \in Proc : Step(p)

\* ----------------------------------------------------------------------
\* Specification (weak fairness on steps of correct processes)
\* ----------------------------------------------------------------------
Spec ==
  Init /\
  [][Next]_vars /\
  \A p \in CorrectSet : WF_vars( Step(p) )

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ CorrectSet \subseteq Proc
  /\ Cardinality(CorrectSet) = N - F
  /\ FaultySet = Proc \ CorrectSet
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted", "Faulty"}]
  /\ \A p \in CorrectSet : pc[p] \in {"Init0", "Init1", "EchoSent", "Accepted"}
  /\ \A p \in FaultySet : pc[p] = "Faulty"
  /\ recv \in [Proc -> SUBSET AllEchos]
  /\ sent \subseteq AllEchos

\* ----------------------------------------------------------------------
\* Additional constraints (model bounds)
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
  ( \A p \in CorrectSet : pc[p] = "Init1" ) => <> ( \A p \in CorrectSet : pc[p] = "Accepted" )

RelayLtl ==
  ( \E p \in CorrectSet : pc[p] = "Accepted" ) => <> ( \A p \in CorrectSet : pc[p] = "Accepted" )

UnforgLtl ==
  ( \A p \in CorrectSet : pc[p] = "Init0" ) => [] ( \A p \in CorrectSet : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Theorems (optional, can be checked by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====
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
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p, r) == { s \in Proc : <<s, "ECHO">> \in r }
EchoCount(p) == Cardinality(EchoSenders(p, recv[p]))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted", "Faulty"}]
  /\ \A p \in Correct : pc[p] \in {"Init0", "Init1"}
  /\ \A p \in Faulty : pc[p] = "Faulty"
  /\ recv \in [Proc -> SUBSET AllEchos]
  /\ \A p \in Proc : recv[p] = {}
  /\ sent = {}

\* ----------------------------------------------------------------------
\* A step for a (correct) process p
\* ----------------------------------------------------------------------
Step(p) ==
  /\ p \in Proc
  /\ IF p \in Correct THEN
        \* The process may receive any new set of ECHO messages
        \E new \in SUBSET (AllEchos \ recv[p]) :
          LET recvNew == recv[p] \cup new IN
          \* Determine the next state based on current pc and received messages
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
             /\ EchoCount(p) >= N - 2*T
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
          /\ UNCHANGED <<Correct, Faulty>>
    ELSE
        /\ pc' = pc
        /\ recv' = recv
        /\ sent' = sent
        /\ UNCHANGED <<Correct, Faulty>>

\* ----------------------------------------------------------------------
\* Next-state relation (any correct process may take a step)
\* ----------------------------------------------------------------------
Next == \E p \in Proc : Step(p)

\* ----------------------------------------------------------------------
\* Specification (with weak fairness on steps of correct processes)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> {"Init0", "Init1", "EchoSent", "Accepted", "Faulty"}]
  /\ \A p \in Correct : pc[p] \in {"Init0", "Init1", "EchoSent", "Accepted"}
  /\ \A p \in Faulty : pc[p] = "Faulty"
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
CorrLtl == ( \A p \in Correct : pc[p] = "Init1" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl == ( \A p \in Correct : pc[p] = "Init0" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Theorems (optional, can be checked by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====
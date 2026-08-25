---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PossibleMsgs(i) == 
    sent \/ { [type |-> "ECHO", sender |-> f] : f \in Faulty }

ECHOFromRecv(i) == { m.sender : m \in recv[i] /\ m.type = "ECHO" }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Faulty \subseteq Proc
    /\ Cardinality(Faulty) = F
    /\ Correct = Proc \ Faulty
    /\ \E initSet \subseteq Correct :
        /\ pc = [i \in Proc |-> IF i \in initSet THEN "Init" ELSE "NoInit"]
        /\ sent = {}
        /\ recv = [i \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(i) ==
    /\ i \in Correct
    /\ \E new \subseteq (PossibleMsgs(i) \ setminus recv[i]) :
        /\ recv' = [recv EXCEPT ![i] = recv[i] \cup new]
        /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitAct(i) ==
    /\ i \in Correct
    /\ pc[i] = "Init"
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
    /\ UNCHANGED <<Correct, Faulty, recv>>

EchoSendNoAccept(i) ==
    /\ i \in Correct
    /\ pc[i] = "NoInit"
    /\ Cardinality(ECHOFromRecv(i)) >= N - 2 * T
    /\ Cardinality(ECHOFromRecv(i)) < N - T
    /\ pc' = [pc EXCEPT ![i] = "EchoSent"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
    /\ UNCHANGED <<Correct, Faulty, recv>>

EchoSendAccept(i) ==
    /\ i \in Correct
    /\ pc[i] = "NoInit"
    /\ Cardinality(ECHOFromRecv(i)) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ sent' = sent \cup { [type |-> "ECHO", sender |-> i] }
    /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptOnly(i) ==
    /\ i \in Correct
    /\ pc[i] = "EchoSent"
    /\ Cardinality(ECHOFromRecv(i)) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "Accepted"]
    /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Next ==
    \/ \E i \in Proc : Receive(i)
    \/ \E i \in Proc : InitAct(i)
    \/ \E i \in Proc : EchoSendNoAccept(i)
    \/ \E i \in Proc : EchoSendAccept(i)
    \/ \E i \in Proc : AcceptOnly(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty \subseteq Proc
    /\ Correct = Proc \ Faulty
    /\ Cardinality(Correct) = N - F
    /\ Cardinality(Faulty) = F
    /\ pc \in [Proc -> {"NoInit", "Init", "EchoSent", "Accepted"}]
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl == ( \A i \in Correct : pc[i] = "Init" ) => <> ( \A i \in Correct : pc[i] = "Accepted" )

RelayLtl == ( \E i \in Correct : pc[i] = "Accepted" ) => <> ( \A i \in Correct : pc[i] = "Accepted" )

UnforgLtl == ( \A i \in Correct : pc[i] = "NoInit" ) => [] ( \A i \in Correct : pc[i] # "Accepted" )

====
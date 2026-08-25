---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"ECHO"}, from : 1..N]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, Sent

vars == <<Correct, Faulty, pc, recv, Sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.from : m \in recv[p] /\ m.type = "ECHO" }

AllMessages == { [type |-> "ECHO", from |-> q] : q \in 1..N }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq 1..N
  /\ Cardinality(Correct) = N - F
  /\ Faulty = (1..N) \ Correct
  /\ pc \in [1..N -> {"NoInit", "Init", "Echo", "Accept", "Faulty"}]
  /\ \A p \in Correct : pc[p] \in {"NoInit", "Init"}
  /\ \A p \in Faulty : pc[p] = "Faulty"
  /\ recv = [p \in 1..N |-> {}]
  /\ Sent = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
  /\ p \in Correct
  /\ UNCHANGED <<Correct, Faulty, pc, Sent>>
  /\ \E new \in SUBSET AllMessages :
        recv' = [recv EXCEPT ![p] = recv[p] \cup new]

SendEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "Init"
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoCond(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - 2 * T
  /\ Cardinality(EchoSenders(p)) < N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc' = [pc EXCEPT ![p] = "Echo"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAndAcceptCond(p) ==
  /\ p \in Correct
  /\ pc[p] = "NoInit"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ Sent' = Sent \cup { [type |-> "ECHO", from |-> p] }
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ pc[p] = "Echo"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED <<Correct, Faulty, recv, Sent>>

Next ==
  \/ \E p \in Correct : Receive(p)
  \/ \E p \in Correct : SendEcho(p)
  \/ \E p \in Correct : SendEchoCond(p)
  \/ \E p \in Correct : SendEchoAndAcceptCond(p)
  \/ \E p \in Correct : AcceptAfterEcho(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq 1..N
  /\ Faulty = (1..N) \ Correct
  /\ pc \in [1..N -> {"NoInit", "Init", "Echo", "Accept", "Faulty"}]
  /\ recv \in [1..N -> SUBSET Message]
  /\ Sent \subseteq Message
  /\ \A m \in Sent : m.type = "ECHO" /\ m.from \in 1..N
  /\ \A p \in 1..N : \A m \in recv[p] : m.type = "ECHO" /\ m.from \in 1..N

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
CorrLtl == ( \A p \in Correct : pc[p] = "Init" ) => <> ( \A p \in Correct : pc[p] = "Accept" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accept" ) => <> ( \A p \in Correct : pc[p] = "Accept" )

UnforgLtl == ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accept" )
=============================================================================
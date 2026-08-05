---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, rcv, sent

vars == <<correct, faulty, pc, rcv, sent>>

Echos == [type : {"ECHO"}, from : 1..N]
Msgs == { [type |-> "ECHO", from |-> s] : s \in 1..N }

InitBroad == {1, 2}
NonBroad == {3, 4}

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ correct \cap faulty = {}
    /\ pc \in [1..N -> {"nc", "bro", "echoing", "done"}]
    /\ rcv \in [1..N -> SUBSET Msgs]
    /\ sent \subseteq Msgs

\* Non-broadcast case: no correct process receives the broadcaster's INIT. The
\* model is checked both with and without this initialization.
Init ==
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> IF p \in InitBroad THEN "bro" ELSE "nc"]
    /\ rcv = [p \in 1..N |-> {}]
    /\ sent = {}

InitQuiet ==
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> "nc"]
    /\ rcv = [p \in 1..N |-> {}]
    /\ sent = {}

\* A correct process receives any messages it can from correct and faulty senders.
Receive(p) ==
    /\ pc[p] \in {"nc", "bro"}
    /\ \E m \subseteq (sent \cup Msgs) : rcv' = [rcv EXCEPT ![p] = @ \cup m]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A process that got the broadcaster's INIT immediately accepts and ECHOs.
AckFromInit(p) ==
    /\ pc[p] = "bro"
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p]}
    /\ UNCHANGED <<correct, faulty, rcv>>

\* Below-threshold: send ECHO but do not yet accept.
Echo3(p) ==
    /\ pc[p] = "nc"
    /\ Cardinality({ m \in rcv[p] : m.type = "ECHO" }) >= N - 2 * T
    /\ Cardinality({ m \in rcv[p] : m.type = "ECHO" }) < N - T
    /\ pc' = [pc EXCEPT ![p] = "echoing"]
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p]}
    /\ UNCHANGED <<correct, faulty, rcv>>

\* At-threshold: send ECHO and accept.
Echo4(p) ==
    /\ pc[p] = "nc"
    /\ Cardinality({ m \in rcv[p] : m.type = "ECHO" }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ sent' = sent \cup {[type |-> "ECHO", from |-> p]}
    /\ UNCHANGED <<correct, faulty, rcv>>

\* After sending ECHO, a process accepts once it has seen enough ECHOs.
Accept(p) ==
    /\ pc[p] = "echoing"
    /\ Cardinality({ m \in rcv[p] : m.type = "ECHO" }) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<correct, faulty, rcv, sent>>

Next ==
    \E p \in 1..N :
        \/ Receive(p)
        \/ AckFromInit(p)
        \/ Echo3(p)
        \/ Echo4(p)
        \/ Accept(p)

Spec ==
    /\ Init \/ InitQuiet
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N : Receive(p))
    /\ WF_vars(\E p \in 1..N : AckFromInit(p))
    /\ WF_vars(\E p \in 1..N : Echo3(p))
    /\ WF_vars(\E p \in 1..N : Echo4(p))
    /\ WF_vars(\E p \in 1..N : Accept(p))

CorrLtl == (\A p \in correct : pc[p] = "bro") ~> (\A p \in correct : pc[p] = "done")
RelayLtl == (\E p \in correct : pc[p] = "done") ~> (\A p \in correct : pc[p] = "done")
UnforgLtl == (~\A p \in correct : pc[p] = "bro") ~> (~\E p \in correct : pc[p] = "done")

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

====
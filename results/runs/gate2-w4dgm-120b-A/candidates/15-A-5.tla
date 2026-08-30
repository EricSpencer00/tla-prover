---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process is either correct or faulty (never both); one of the two
\* partitions is chosen nondeterministically at init, with F faulty.
ASSUME F \in 0..T /\ N > 3 * T

Message == {"ECHO"}
Node == 1..N

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

Bump(i) == [pc[i] EXCEPT ! = IF @ = "rcvd" THEN "accept" ELSE "echoed"]

TypeOK ==
  /\ correct \subseteq Node
  /\ faulty \subseteq Node
  /\ pc \in [Node -> {"rcvd", "nosig", "echoed", "accept"}]
  /\ inbox \in [Node -> SUBSET (Node \X Message)]
  /\ sent \subseteq (Node \X Message)

\* Unforgeability: no accept unless at least one correct process broadcast.
FCConstraints ==
  /\ (correct = {} => \A i \in Node : pc[i] # "accept")
  /\ pc' \in [Node -> {"rcvd", "nosig", "echoed", "accept"}]
  /\ correct' \subseteq Node
  /\ faulty' \subseteq Node
  /\ sent' \subseteq (Node \X Message)
  /\ inbox' \in [Node -> SUBSET (Node \X Message)]

Init ==
  /\ correct = {i \in Node : i <= N - F}
  /\ faulty = Node \ correct
  /\ pc = [i \in Node |-> IF i <= N - F THEN "rcvd" ELSE "nosig"]
  /\ inbox = [i \in Node |-> {}]
  /\ sent = {}

InitNoBroadcast ==
  /\ correct = {i \in Node : i <= N - F}
  /\ faulty = Node \ correct
  /\ pc = [i \in Node |-> "nosig"]
  /\ inbox = [i \in Node |-> {}]
  /\ sent = {}

\* A correct process receives a subset of all possible messages and acts
\* on them immediately (bounded-buffer modelling of recv-and-act).
RecvAndAct(i) ==
  /\ pc[i] \in {"rcvd", "nosig"}
  /\ \E m \in SUBSET (Node \X Message) :
       inbox' = [inbox EXCEPT ![i] = m]
  /\ pc' = IF pc[i] = "rcvd" THEN Bump(i) ELSE pc[i]
  /\ sent' = IF pc[i] = "rcvd" THEN sent \cup {<<i, "ECHO">>} ELSE sent
  /\ UNCHANGED <<correct, faulty>>

\* Below N-T echoes a process cannot yet accept, but it still sends ECHO.
Echo(i) ==
  /\ pc[i] = "nosig"
  /\ Cardinality(inbox[i]) >= N - 2 * T
  /\ Cardinality(inbox[i]) < N - T
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ pc' = "echoed"
  /\ UNCHANGED <<correct, faulty, inbox>>

Accept(i) ==
  /\ pc[i] \in {"nosig", "echoed"}
  /\ Cardinality(inbox[i]) >= N - T
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ pc' = "accept"
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A process that has already echoed may still be waiting on the rest of
\* the group; it accepts once the quorum threshold is reached.
LateAccept(i) ==
  /\ pc[i] = "echoed"
  /\ Cardinality(inbox[i]) >= N - T
  /\ pc' = "accept"
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

Relayed == \E i \in Node : RecvAndAct(i) \/ LateAccept(i)

Next ==
  \/ Relayed
  \/ \E i \in Node : Echo(i) \/ Accept(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Relayed)

\* Safety: once every correct process has broadcast, every correct
\* process eventually accepts.
CorrLtl == (\A i \in correct : pc[i] = "rcvd") ~> (\A i \in correct : pc[i] = "accept")

\* Liveness: acceptance always spreads to the whole correct group.
RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

\* Unforgeability: no acceptance without at least one correct broadcast.
UnforgLtl == (\A i \in correct : pc[i] # "accept") ~> (\E i \in correct : pc[i] = "accept")

====
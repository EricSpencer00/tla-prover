---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct and faulty (Byzantine) processes partition the system; the
\* broadcast is implicit in each process's initial state (init broadcast),
\* so no dedicated broadcaster is modeled.
Processes == 1..N
Locations == {"nobroadcast", "broadcast", "echoed", "passed"}

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

RECURSIVE Intersect(_, _)
Intersect(S, T) == IF S = {} THEN {} ELSE LET x == CHOOSE y \in S : TRUE IN
  IF x \in T THEN {x} \cup Intersect(S \ {x}, T) ELSE Intersect(S \ {x}, T)

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = { (N - F + 1)..N }
  /\ pc = [p \in Processes |-> IF p \in correct THEN "broadcast" ELSE "nobroadcast"]
  /\ inbox = [p \in Processes |-> {}]
  /\ sent = {}

Receive(p, S) ==
  /\ p \in correct
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ S \subseteq { <<q, "ECHO">> : q \in correct \/ faulty }
  /\ inbox' = [inbox EXCEPT ![p] = @ \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "broadcast"
  /\ pc' = [pc EXCEPT ![p] = "passed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

EchoThreshold(p) ==
  /\ p \in correct
  /\ pc[p] \in {"nobroadcast", "broadcast"}
  /\ Cardinality(Intersect(inbox[p], { <<q, "ECHO">> : q \in Processes })) >= N - 2 * T
  /\ Cardinality(Intersect(inbox[p], { <<q, "ECHO">> : q \in Processes })) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

EchoAccept(p) ==
  /\ p \in correct
  /\ pc[p] \in {"nobroadcast", "broadcast"}
  /\ Cardinality(Intersect(inbox[p], { <<q, "ECHO">> : q \in Processes })) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "passed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

LateAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality(Intersect(inbox[p], { <<q, "ECHO">> : q \in Processes })) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "passed"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

\* One action per correct process: either it receives new messages or it
\* acts on what it already has (echoing, accepting, or both).
ReceiveAndAct(p) ==
  \/ Receive(p, {})
  \/ EchoThreshold(p)
  \/ EchoAccept(p)
  \/ LateAccept(p)

Next ==
  \E p \in Processes : ReceiveAndAct(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ReceiveAndAct(1))
  /\ WF_vars(ReceiveAndAct(2))

\* Safety: everything stays inside its domain, so no action creates an
\* illegal value that could masquerade as a correct message.
TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty \subseteq Processes
  /\ pc \in [Processes -> Locations]
  /\ inbox \in [Processes -> SUBSET [1..N \X {"ECHO"}]]
  /\ sent \subseteq [1..N \X {"ECHO"}]

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ \A p \in Processes : pc[p] \in Locations

\* Liveness: with a full broadcast all correct processes eventually accept.
CorrLtl ==
  ( \A p \in correct : pc[p] = "broadcast" )
    ~> ( \A p \in correct : pc[p] = "passed" )

RelayLtl ==
  ( \E p \in correct : pc[p] = "passed" )
    ~> ( \A p \in correct : pc[p] = "passed" )

\* Unforgeability: with no correct broadcaster (all start without the init
\* message) no correct process ever reaches the accept state.
UnforgLtl ==
  ( \A p \in correct : pc[p] # "broadcast" )
    ~> ( \A p \in correct : pc[p] # "passed" )

====
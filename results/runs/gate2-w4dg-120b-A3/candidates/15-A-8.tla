---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: no init received, init received, echo sent, accepted.
Locations == {"none", "recv", "echoed", "accepted"}

VARIABLES correct, faulty, pc, inbox, sentmsg
vars == << correct, faulty, pc, inbox, sentmsg>>

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> Locations]
  /\ inbox \in [1..N -> SUBSET [from: 1..N, ty: {"ECHO"}]]
  /\ sentmsg \subseteq [to: 1..N, ty: {"ECHO"}]

\* Unforgeability is checked over a restricted initial state: no broadcaster
\* started the protocol, so a correct process must never accept.
FCConstraints == \A p \in 1..N : pc[p] \in Locations

Init ==
  /\ correct = {1..(N - F)}
  /\ pc = [p \in 1..N |-> IF p <= (N - F) THEN "recv" ELSE "none"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sentmsg = {}

\* An unrestricted initial state is also available; the safety property must
\* hold under both, so the model is driven to the restricted case for checking.
AltInit ==
  /\ correct = {1..(N - F)}
  /\ pc = [p \in 1..N |-> "none"]
  /\ inbox = [p \in 1..N |-> {}]
  /\ sentmsg = {}

\* A correct process receives a new set of messages, including arbitrary
\* Byzantine contributions.
Receive(p, msgs) ==
  /\ p \in correct
  /\ msgs # {}
  /\ msgs \subseteq (sentmsg \cup [to |-> p, ty |-> "ECHO"])
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup msgs]
  /\ UNCHANGED << correct, pc, sentmsg >>

\* A process that received the broadcaster's INIT accepts immediately.
RecvAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "recv"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentmsg' = sentmsg \cup [to |-> q, ty |-> "ECHO" : q \in 1..N]
  /\ UNCHANGED << correct, inbox >>

\* A process with no echo yet may echo once it has gathered enough but not all.
EchoLate(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality({m.from : m \in inbox[p]}) >= (N - (2 * T))
  /\ Cardinality({m.from : m \in inbox[p]}) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sentmsg' = sentmsg \cup [to |-> q, ty |-> "ECHO" : q \in 1..N]
  /\ UNCHANGED << correct, inbox >>

\* A process with no echo yet accepts immediately once it has a quorum.
EchoQuorum(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality({m.from : m \in inbox[p]}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentmsg' = sentmsg \cup [to |-> q, ty |-> "ECHO" : q \in 1..N]
  /\ UNCHANGED << correct, inbox >>

\* A process that already echoed accepts once it has a quorum.
AcceptLate(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality({m.from : m \in inbox[p]}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, inbox, sentmsg >>

\* Weak fairness lets each receive-and-act step run forever if it can.
RecFair(p) == Receive(p, [to |-> p, ty |-> "ECHO"])
AcqFair(p) == RecFair(p) \/ RecFair(p) \/ RecFair(p) \/ EchoLate(p) \/ EchoQuorum(p) \/ AcceptLate(p) \/ RecvAccept(p)

Next ==
  \/ \E p \in 1..N : RecFair(p) \/ AcqFair(p)
  \/ AltInit

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(RecFair(p)) /\ WF_vars(AcqFair(p))

\* Correctness: if every correct process began with the broadcast, all accept.
CorrLtl == (\A p \in correct : pc[p] = "recv") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
UnforgLtl == (\A p \in correct : pc[p] = "none") ~> (\A p \in correct : pc[p] # "accepted")

====
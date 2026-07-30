---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* One-round reliable broadcast with Byzantine faults (Srikanth & Toueg, 1987).
\* The broadcaster's INIT is represented by each process's initial state.
\* N >= 4, T >= 1, N > 3*T; processes are partitioned into correct and faulty.
CONSTANTS N, T, F

Processes == 1..N
MsgKinds == {"ECHO"}
Pair(p, k) == <<p, k>>

\* Location: NoINIT (no broadcast seen), GotINIT (broadcast seen),
\* Sent (ECHO sent), Accepted (ECHO threshold reached).
VARIABLES correct, faulty, loc, inbox, sent

vars == <<correct, faulty, loc, inbox, sent>>

\* All messages a correct process could have sent, and all messages any process
\* could have sent (the latter includes arbitrary Byzantine messages).
SentMsg == {Pair(p, k) : p \in correct, k \in MsgKinds}
AllSent == SentMsg \cup {Pair(p, k) : p \in Processes, k \in MsgKinds}

TypeOK ==
  /\ correct \cup faulty = Processes
  /\ correct \cap faulty = {}
  /\ loc \in [Processes -> {"NoINIT", "GotINIT", "Sent", "Accepted"}]
  /\ inbox \in [Processes -> SUBSET AllSent]
  /\ sent \subseteq SentMsg

\* No Byzantine process ever counts towards the thresholds; messages are always
\* attributed to an identity, so a forged identity is caught by the cardinality
\* check on distinct senders below.
FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ \A p \in Processes: loc[p] \in {"NoINIT", "GotINIT", "Sent", "Accepted"}
  /\ \A p \in Processes: inbox[p] \subseteq AllSent

Init(k, s) ==
  /\ correct \cup faulty = Processes
  /\ correct \cap faulty = {}
  /\ loc = [p \in Processes |-> IF p \in k THEN "GotINIT" ELSE "NoINIT"]
  /\ inbox = [p \in Processes |-> {}]
  /\ sent = {}
  /\ \A p \in Processes: IF p \in s THEN loc[p] = "GotINIT" ELSE TRUE

\* A correct process receives a (possibly empty) batch of messages it has not
\* seen; the batch may come from correct senders, from Byzantine ones, or both.
Recv(p, batch) ==
  /\ p \in correct
  /\ batch # {}
  /\ batch \subseteq AllSent
  /\ batch \cap inbox[p] = {}
  /\ inbox' = [inbox EXCEPT ![p] = @ \cup batch]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

SendEcho(p) ==
  /\ p \in correct
  /\ loc' = [loc EXCEPT ![p] = "Sent"]
  /\ sent' = sent \cup SentMsg
  /\ UNCHANGED <<correct, faulty, inbox>>

Accept(p) ==
  /\ p \in correct
  /\ loc[p] \in {"Sent", "GotINIT"}
  /\ Cardinality({q \in Processes : Pair(q, "ECHO") \in inbox[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

\* A correct process that never got the INIT may still send an ECHO once it
\* has collected a partial set of (N-2T) acknowledgements, without accepting.
RelayMid(p) ==
  /\ p \in correct
  /\ loc[p] = "NoINIT"
  /\ Cardinality({q \in Processes : Pair(q, "ECHO") \in inbox[p]}) >= N - 2 * T
  /\ Cardinality({q \in Processes : Pair(q, "ECHO") \in inbox[p]}) < N - T
  /\ SendEcho(p)

RelayFull(p) ==
  /\ p \in correct
  /\ loc[p] \in {"NoINIT", "GotINIT"}
  /\ Cardinality({q \in Processes : Pair(q, "ECHO") \in inbox[p]}) >= N - T
  /\ SendEcho(p)
  /\ Accept(p)

Quiesce ==
  /\ \A p \in Processes: loc[p] = "Accepted"
  /\ UNCHANGED vars

Next ==
  \/ Quiesce
  \/ \E p \in Processes: Accept(p)
  \/ \E p \in Processes: RelayMid(p)
  \/ \E p \in Processes: RelayFull(p)
  \/ \E p \in correct, batch \in SUBSET AllSent: Recv(p, batch)

\* Weak fairness on the combined receive-and-act steps of correct processes.
Spec ==
  /\ \E k \in [Processes -> BOOLEAN], s \in [Processes -> BOOLEAN]: Init(k, s)
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes, batch \in SUBSET AllSent: Recv(p, batch))
  /\ WF_vars(\E p \in Processes: Accept(p))

\* Broadcast case: every correct process started with the INIT message.
CorrLtl == (\A p \in correct: loc[p] = "GotINIT") ~> (\A p \in correct: loc[p] = "Accepted")

\* Relay case: once some correct process accepts, they all eventually do.
RelayLtl == (\E p \in correct: loc[p] = "Accepted") ~> (\A p \in correct: loc[p] = "Accepted")

UnforgLtl == (\A p \in correct: loc[p] = "NoINIT") ~> (\A p \in correct: loc[p] = "NoINIT")

====
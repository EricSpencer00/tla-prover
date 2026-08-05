---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A one-round reliable broadcast (Figure 7, Srikanth \& Toueg, 1987) over a
\* N-process network where up to F (<= T) processes may be Byzantine.  A
\* correct process accepts when it sees a quorum of ECHO messages; Byzantine
\* processes may inject arbitrary ECHO messages.  The two-bit control word
\* runs: 0 = no INIT message, 1 = INIT received, 2 = sent ECHO, 3 = accepted.

Processes == 0..(N-1)
Ids == 0..(N-1)
Msgs == {"echo"}

VARIABLES correct, faulty, loc, msgs, sentMsgs

vars == <<correct, faulty, loc, msgs, sentMsgs>>

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty = Processes \ correct
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ \A p \in Processes : loc[p] \in 0..3
  /\ \A p \in Processes : msgs[p] \subseteq (Ids \X Msgs)
  /\ sentMsgs \subseteq (Ids \X Msgs)
  /\ Cardinality(sentMsgs) <= N

Init ==
  /\ \E g \in {1, 0} : g \in {0, 1} /\ loc = [p \in Processes |-> g]
  /\ correct = CHOOSE S \in {S \in SUBSET Processes : Cardinality(S) = N - F}
  /\ faulty = Processes \ correct
  /\ msgs = [p \in Processes |-> {}]
  /\ sentMsgs = {}

\* A correct process non-deterministically receives some new messages, drawn
\* from all correct-send messages plus all possible Byzantine messages.
Receive(p) ==
  /\ p \in correct
  /\ loc[p] < 3
  /\ \E new \in SUBSET (sentMsgs \cup (Ids \X Msgs)) :
       msgs' = [msgs EXCEPT ![p] = msgs[p] \cup new]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* A correct broadcaster that already knows the INIT immediately accepts and
\* broadcasts its ECHO to everyone.
BroadcastInit(p) ==
  /\ p \in correct
  /\ loc[p] = 1
  /\ loc' = [loc EXCEPT ![p] = 3]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* A correct process that has not broadcast yet may do so once it has collected
\* enough (but not a quorum) ECHO messages from distinct senders.
BroadcastLow(p) ==
  /\ p \in correct
  /\ loc[p] = 0
  /\ Cardinality({q \in Processes : <<q, "echo">> \in msgs[p]}) >= N - 2 * T
  /\ Cardinality({q \in Processes : <<q, "echo">> \in msgs[p]}) < N - T
  /\ loc' = [loc EXCEPT ![p] = 2]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* A correct process that collects a quorum of ECHO messages both broadcasts
\* and accepts together.
BroadcastQuorum(p) ==
  /\ p \in correct
  /\ loc[p] = 0
  /\ Cardinality({q \in Processes : <<q, "echo">> \in msgs[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = 3]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* A correct process that has already broadcast accepts on seeing a quorum.
Accept(p) ==
  /\ p \in correct
  /\ loc[p] = 2
  /\ Cardinality({q \in Processes : <<q, "echo">> \in msgs[p]}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = 3]
  /\ UNCHANGED <<correct, faulty, msgs, sentMsgs>>

Next ==
  \/ \E p \in Processes : Receive(p)
  \/ \E p \in Processes : BroadcastInit(p)
  \/ \E p \in Processes : BroadcastLow(p)
  \/ \E p \in Processes : BroadcastQuorum(p)
  \/ \E p \in Processes : Accept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Processes :
       /\ (loc[p] = 0 /\ loc[p] < 3) ~> (loc[p] = 3)
       /\ (loc[p] = 1 /\ loc[p] < 3) ~> (loc[p] = 3)
       /\ (loc[p] = 2 /\ loc[p] < 3) ~> (loc[p] = 3)
       WF_vars(Receive(p))

\* Unforgeability: if no correct process initially broadcast, no correct
\* process ever accepts, no matter what the Byzantine processes inject.
UnforgLtl == (\A p \in correct : loc[p] # 1) ~> (\A p \in correct : loc[p] # 3)

CorrLtl == (\A p \in correct : loc[p] = 1) ~> (\A p \in correct : loc[p] = 3)
RelayLtl == (\E p \in correct : loc[p] = 3) ~> (\A p \in correct : loc[p] = 3)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====
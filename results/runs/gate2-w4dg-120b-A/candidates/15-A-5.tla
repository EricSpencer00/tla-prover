---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

\* A process's control location: whether it received the INIT message,
\* whether it has sent an ECHO, or whether it has accepted.
Locs == {"initRecv", "initNotRec", "sentEcho", "accepted"}

\* ECHO messages are tagged by sender identity; messages from Byzantine
\* processes are modeled as unconstrained in the receive action.
Msgs == [from: 1..N, ty: {"ECHO"}]

VARIABLES correct, faulty, loc, recvMsgs, sentMsgs

vars == <<correct, faulty, loc, recvMsgs, sentMsgs>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locs]
  /\ recvMsgs \in [1..N -> SUBSET Msgs]
  /\ sentMsgs \subseteq Msgs

\* Safety: every correct process that accepts has a genuine ECHO feed from
\* at least N-T distinct senders, which no correct process can ever forge.
AcceptWithDistinctFeed ==
  \A p \in correct : loc[p] = "accepted" =>
    Cardinality({m.from : m \in recvMsgs[p]}) >= (N - T)

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ correct
  /\ loc = [p \in 1..N |-> IF p <= (N - F) THEN "initRecv" ELSE "initNotRec"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

\* The restricted initial state: no correct process received the INIT.
NoInitAllNotRec ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ correct
  /\ loc = [p \in 1..N |-> "initNotRec"]
  /\ recvMsgs = [p \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process receives some new messages (both correct and Byzantine).
ReceiveMsgs(p) ==
  /\ p \in correct
  /\ loc[p] # "accepted"
  /\ \E S \subseteq (sentMsgs \cup Msgs) : recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup S]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* A correct process that already received the broadcaster's INIT accepts and
\* sends ECHO immediately (the one-round broadcast shortcut).
AcceptAndEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "initRecv"
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[from |-> p, ty |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process with no feed yet sends ECHO once it has N-2T distinct
\* senders' ECHOs, but does not accept until N-T.
EchoOnPartialFeed(p) ==
  /\ p \in correct
  /\ loc[p] = "initNotRec"
  /\ Cardinality({m.from : m \in recvMsgs[p]}) >= (N - 2 * T)
  /\ Cardinality({m.from : m \in recvMsgs[p]}) < (N - T)
  /\ loc' = [loc EXCEPT ![p] = "sentEcho"]
  /\ sentMsgs' = sentMsgs \cup {[from |-> p, ty |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process with no feed yet both sends ECHO and accepts once it
\* has a full N-T distinct senders' ECHOs.
EchoAndAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "initNotRec"
  /\ Cardinality({m.from : m \in recvMsgs[p]}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[from |-> p, ty |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process that already sent ECHO accepts once it has N-T distinct
\* senders' ECHOs.
AcceptOnFullFeed(p) ==
  /\ p \in correct
  /\ loc[p] = "sentEcho"
  /\ Cardinality({m.from : m \in recvMsgs[p]}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

\* Any correct process can receive and act, so fairness is per-process.
ProcessStep(p) == ReceiveMsgs(p) \/ AcceptAndEcho(p) \/ EchoOnPartialFeed(p) \/ EchoAndAccept(p) \/ AcceptOnFullFeed(p)

Next ==
  \/ \E p \in 1..N : ProcessStep(p)
  \/ NoInitAllNotRec

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(ProcessStep(p))

CorrLtl == <>(\A p \in correct : loc[p] = "accepted")
RelayLtl == (<> ( \E p \in correct : loc[p] = "accepted")) ~> (\A p \in correct : loc[p] = "accepted")

UnforgLtl == ( ( \A p \in correct : loc[p] = "initNotRec") ) ~> ( \A p \in correct : loc[p] = "initNotRec")
FCConstraints == AcceptWithDistinctFeed

====
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* This module implements the one-round reliable broadcast protocol from
\* Srikanth & Toueg (1987), Figure 7, for a system with Byzantine faults.
\* The broadcaster is modeled as an initial value per process: either a
\* process started with the message already in hand (the broadcast case)
\* or it started empty and must rely on others' echoes (the no-broadcast
\* case where every correct process is itself an equivocation). The message
\* set always includes every message a correct process could possibly
\* have sent, plus an arbitrary (possibly empty) set of messages from
\* Byzantine processes, so the actual set received is a nondeterministic
\* subset of that—a valid network reordering that also models malicious
\* senders dropping or fabricating messages. The unforgeability property
\* below is the main safety claim: with no correct initial broadcast, no
\* correct process ever accepts the message.
CONSTANTS N, T, F

\* Types: loc is the process PC (waiting, echoing, accepted); msgs is the
\* inbox per process; sent is the set of messages any correct process
\* actually sent. EchoSet(p) extracts the echo-senders currently present
\* in p's inbox.
None == 0
Procs == 1..N
Senders == {1..N}
Echoes == {"echo"}
SentMsgs == [to : Procs, typ : Echoes]

Loc == {"have", "none", "sent", "acpt"}

EchoSet(p) == { m.to : m \in { x \in msgs[p] : x.typ = "echo" } }

VARIABLES correct, faulty, loc, msgs, sent

vars == <<correct, faulty, loc, msgs, sent>>

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty = Procs \ correct
  /\ loc \in [Procs -> Loc]
  /\ msgs \in [Procs -> SUBSET SentMsgs]
  /\ sent \subseteq SentMsgs

Init ==
  /\ correct = CHOOSE S \in {S \in SUBSET Procs : Cardinality(S) = N - F} : TRUE
  /\ faulty = Procs \ correct
  /\ sent = {}
  /\ \E s \in Procs, S \in {S \in SUBSET Procs : s \in S /\ Cardinality(S) = N} :
       /\ loc = [p \in Procs |-> IF p \in S THEN "have" ELSE "none"]
       /\ msgs = [p \in Procs |-> {}]

NoBroadInit ==
  /\ correct = CHOOSE S \in {S \in SUBSET Procs : Cardinality(S) = N - F} : TRUE
  /\ faulty = Procs \ correct
  /\ sent = {}
  /\ \E s \in Procs, S \in {S \in SUBSET Procs : s \in S /\ Cardinality(S) = N} :
       loc = [p \in Procs |-> IF p \in S THEN "have" ELSE "none"]
  /\ msgs = [p \in Procs |-> {}]

\* Every message a correct process could have sent, plus an arbitrary
\* set of messages from Byzantine processes (drops, reorderings, or
\* outright fabrications, since a faulty process may be silent or noisy).
AllMsgs(p) ==
  { m \in sent \cup SentMsgs : m.to = p } \cup
    { m \in SentMsgs : m.to = p /\ m.to \in faulty }

\* A correct process may receive any nonempty subset of that combined set.
Recv(p, M) ==
  /\ M # {}
  /\ M \subseteq AllMsgs(p)
  /\ msgs' = [msgs EXCEPT ![p] = @ \cup M]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A correct process that started with the broadcast in hand accepts and
\* sends its own echo immediately (the one-round "fast path").
Broadcast(p) ==
  /\ p \in correct
  /\ loc[p] = "have"
  /\ loc' = [loc EXCEPT ![p] = "acpt"]
  /\ sent' = sent \cup {[to |-> q, typ |-> "echo"] : q \in Procs}
  /\ UNCHANGED <<correct, faulty, msgs>>

\* Receiving at least N-2T echoes is enough to send an echo, but not yet
\* enough to accept (the "slow path").
Relay(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Cardinality(EchoSet(p)) >= N - 2 * T
  /\ Cardinality(EchoSet(p)) < N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {[to |-> q, typ |-> "echo"] : q \in Procs}
  /\ UNCHANGED <<correct, faulty, msgs>>

AcceptRelay(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Cardinality(EchoSet(p)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "acpt"]
  /\ sent' = sent \cup {[to |-> q, typ |-> "echo"] : q \in Procs}
  /\ UNCHANGED <<correct, faulty, msgs>>

LateAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "sent"
  /\ Cardinality(EchoSet(p)) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "acpt"]
  /\ UNCHANGED <<correct, faulty, msgs, sent>>

Next ==
  \/ \E p \in Procs, M \in SUBSET SentMsgs : Recv(p, M)
  \/ \E p \in Procs : Broadcast(p)
  \/ \E p \in Procs : Relay(p)
  \/ \E p \in Procs : AcceptRelay(p)
  \/ \E p \in Procs : LateAccept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Procs : WF_vars(Recv(p, {m \in SentMsgs : m.to = p})))

NoFairSpec ==
  /\ Init
  /\ [][Next]_vars

\* Unforgeability: without a correct broadcast, no correct process accepts.
UnforgLtl == (\A p \in correct : loc[p] = "none") ~> (\A p \in correct : loc[p] = "acpt")

\* If every correct process started with the broadcast, they all accept.
CorrLtl == (\A p \in correct : loc[p] = "have") ~> (\A p \in correct : loc[p] = "acpt")

\* Once any correct process accepts, they all eventually accept.
RelayLtl == (\E p \in correct : loc[p] = "acpt") ~> (\A p \in correct : loc[p] = "acpt")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====
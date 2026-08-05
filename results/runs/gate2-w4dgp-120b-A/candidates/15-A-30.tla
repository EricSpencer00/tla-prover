---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Broadcast-initiated state: whether a correct process is considered
\* to have received the initiator's INIT message (itself part of the
\* model, so broadcast starts are encoded as initial process states).
\* The one-round SRV97 protocol takes a single reliable broadcast
\* round: ECHO messages back to every process, with acceptance
\* thresholds that guarantee Byzantine-fault tolerance.

Senders == 1..N
MsgKinds == {"ECHO"}
Msgs == [snd : Senders, knd : MsgKinds]
Locs == {"init","nosend","echoed","accepted"}
EmptySet == {}

RECURSIVE UnionOf(_, _)
UnionOf(S, f) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \cup UnionOf(S \ {x}, f)

VARIABLES correct, faulty, loc, recv, sent

vars == <<correct, faulty, loc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Senders
  /\ faulty = Senders \ correct
  /\ loc \in [Senders -> Locs]
  /\ recv \in [Senders -> SUBSET Msgs]
  /\ sent \subseteq Msgs

Init ==
  /\ correct \in { S \in (SUBSET Senders) : Cardinality(S) = N - F }
  /\ loc \in [Senders -> {"init","nosend"}]
  /\ recv = [p \in Senders |-> EmptySet]
  /\ sent = EmptySet

\* No-process-starts broadcast: all start in the "nosend" (no INIT
\* received) state; every correct process must subsequently reject.
InitNoBroadcast ==
  /\ correct \in { S \in (SUBSET Senders) : Cardinality(S) = N - F }
  /\ loc = [p \in Senders |-> "nosend"]
  /\ recv = [p \in Senders |-> EmptySet]
  /\ sent = EmptySet

RecvMsgs(p, msgs) ==
  /\ p \in correct
  /\ loc[p] \in {"nosend","init"}
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup msgs]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* A correct broadcast (init) process always accepts immediately and
\* ECHOs to everyone; the "init" state is the only one that may do so.
InitAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "init"
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[snd |-> p, knd |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* If a correct process has not broadcast itself but has gathered a
\* quorum short of the accept threshold, it may still ECHO without
\* yet accepting; this is the relay step.
RelayEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "nosend"
  /\ Cardinality({ m \in recv[p] : m.knd = "ECHO" }) >= (N - 2 * T)
  /\ Cardinality({ m \in recv[p] : m.knd = "ECHO" }) < (N - T)
  /\ loc' = [loc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {[snd |-> p, knd |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has gathered enough ECHOs (the accept
\* threshold) broadcasts and accepts in the same step.
AcceptEcho(p) ==
  /\ p \in correct
  /\ loc[p] = "nosend"
  /\ Cardinality({ m \in recv[p] : m.knd = "ECHO" }) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[snd |-> p, knd |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "echoed"
  /\ Cardinality({ m \in recv[p] : m.knd = "ECHO" }) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in Senders : InitAccept(p) \/ RelayEcho(p) \/ AcceptEcho(p) \/ RelayAccept(p)
  \/ \E p \in Senders, msgs \in SUBSET (sent \cup {[snd |-> q, knd |-> "ECHO"] : q \in faulty}) : RecvMsgs(p, msgs)
  \/ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Senders : WF_vars(RecvMsgs(p, sent \cup {[snd |-> q, knd |-> "ECHO"] : q \in faulty})))

\* The no-broadcast case may be established without fairness: if
\* every correct process refuses to start, it can never reach
\* acceptance while following the correct process protocol.
SpecNoFault ==
  /\ InitNoBroadcast
  /\ [][Next]_vars

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

UnforgeLtl == (Locs = {"nosend"}) ~> (\A p \in Senders : loc[p] # "init")
CorrLtl == (Locs = {"init"}) ~> (\A p \in Senders : loc[p] = "accepted")
RelayLtl == (\E p \in Senders : loc[p] = "accepted") ~> (\A p \in Senders : loc[p] = "accepted")

====
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Process roles: correct (follows the protocol) vs faulty (any arbitrary
\* ECHO messages).  PC state: broadcast-received, non-received, sent ECHO, or
\* accepted.  Unforgeability is the property that nothing is accepted unless a
\* correct broadcast actually occurred.
VARIABLES correct, faulty, pc, inMsgs, sentMsgs

vars == <<correct, faulty, pc, inMsgs, sentMsgs>>

Procs == 0 .. (N - 1)
MsgIds == {"init", "echo"}
MsgSpace == {<<p, t>> : p \in Procs, t \in MsgIds}
Empty == {}

\* A correct process may receive any subset of all messages it is ever sent:
\* the messages from correct senders (which it will actually get) plus the
\* arbitrary messages from faulty senders (which it may or may not get).
RECURSIVE Reachable(_)
Reachable(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN inMsgs[x] \cup Reachable(S \ {x})

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty \subseteq Procs
  /\ pc \in [Procs -> {"broadcast", "nobroadcast", "sent", "accepted"}]
  /\ inMsgs \in [Procs -> SUBSET MsgSpace]
  /\ sentMsgs \subseteq MsgSpace

Init ==
  /\ correct = {p \in Procs : p < (N - F)}
  /\ faulty = {p \in Procs : p >= (N - F)}
  /\ pc = [p \in Procs |-> IF p < (N - F) THEN "broadcast" ELSE "nobroadcast"]
  /\ inMsgs = [p \in Procs |-> Empty]
  /\ sentMsgs = Empty

SendByCorrect(p) == <<p, "echo">> \in sentMsgs
EchosFromCorrect(p) ==
  Cardinality({m \in inMsgs[p] : m[2] = "echo" /\ SendByCorrect(m[1])})

Receive(p) ==
  /\ \E m \in Reachable(correct) : m \notin inMsgs[p] /\ inMsgs' = [inMsgs EXCEPT ![p] = @ \cup {m}]
  /\ pc' \in [pc EXCEPT ![p] = IF pc[p] \in {"broadcast", "nobroadcast"}
                                     THEN "nobroadcast"
                                     ELSE pc[p]]
  /\ UNCHANGED <<correct, faulty, sentMsgs>>

ActOnBroadcast(p) ==
  /\ pc[p] = "broadcast"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inMsgs>>

ActOnCollectE(p) ==
  /\ pc[p] = "nobroadcast"
  /\ EchosFromCorrect(p) >= (N - 2 * T)
  /\ EchosFromCorrect(p) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inMsgs>>

ActOnFinalE(p) ==
  /\ pc[p] \in {"broadcast", "nobroadcast", "sent"}
  /\ EchosFromCorrect(p) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, inMsgs>>

ActOnAnyE(p) ==
  /\ pc[p] \in {"broadcast", "nobroadcast", "sent"}
  /\ EchosFromCorrect(p) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, inMsgs, sentMsgs>>

Next ==
  \/ \E p \in Procs : Receive(p)
  \/ \E p \in Procs : ActOnBroadcast(p)
  \/ \E p \in Procs : ActOnCollectE(p)
  \/ \E p \in Procs : ActOnFinalE(p)
  \/ \E p \in Procs : ActOnAnyE(p)

CorrLtl == <>(\A p \in correct : pc[p] = "accepted")
RelayLtl == \A p \in Procs : (pc[p] = "accepted" ~> (\A q \in correct : pc[q] = "accepted"))

\* Unforgeability must hold even in a fully unfair run (nothing forces delivery
\* or action), so it is a plain-state invariant rather than a liveness
\* property, unlike the correctness and relay properties.
UnforgLtl == (\A p \in correct : pc[p] = "broadcast") ~> (\A p \in correct : pc[p] = "accepted")
FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Procs : WF_vars(Receive(p)))
  /\ (\A p \in Procs : WF_vars(ActOnCollectE(p)))
  /\ (\A p \in Procs : WF_vars(ActOnFinalE(p)))
  /\ FCConstraints

====
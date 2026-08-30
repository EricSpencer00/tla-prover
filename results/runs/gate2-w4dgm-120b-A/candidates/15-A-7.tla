---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the Srikanth-Toueg 1-round broadcast protocol;
\* faulty processes may send arbitrary ECHO messages (they can be slow or
\* silent, but are never assumed to send correct ECHO values). The safety
\* property (unforgeability) is a proposition about the reachable state
\* space and holds regardless of weak fairness; the liveness properties
\* do rely on weak fairness of message delivery and processing.

VARIABLES correct, faulty, pc, recv, sent
vars == << correct, faulty, pc, recv, sent >>

MsgType == {"ech"}
Msg == [snd: 0..N-1, tp: MsgType]
Echoes(u) == {m.snd : m \in recv[u]}

TypeOK ==
  /\ correct \subseteq 0..N-1
  /\ faulty \subseteq 0..N-1
  /\ pc \in [0..N-1 -> {"nosend", "broadcast", "nobroadcast", "sent", "accepted"}]
  /\ recv \in [0..N-1 -> SUBSET Msg]
  /\ sent \subseteq Msg

\* Unforgeability: only the correct processes' ECHO messages may ever
\* count toward an acceptance decision, so nothing short of a real
\* broadcast from the correct set can ever convince a correct process.
FCConstraints ==
  /\ (N > 3 * T /\ T >= F /\ F >= 0)
  /\ correct \cup faulty = 0..N-1
  /\ correct \cap faulty = {}
  /\ \A u \in 0..N-1 : pc[u] \in {"nosend", "broadcast", "nobroadcast", "sent", "accepted"}
  /\ \A u \in 0..N-1 : \A m \in recv[u] : m \in sent

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..N-1) \ correct
  /\ \E c \in correct : pc[c] = "broadcast"
  /\ \A u \in 0..N-1 :
       /\ IF u \in correct THEN pc[u] \in {"broadcast", "nobroadcast"} ELSE TRUE
       /\ recv[u] = {}
  /\ sent = {}

InitNoBroadcast ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (0..N-1) \ correct
  /\ \A u \in correct : pc[u] = "nobroadcast"
  /\ \A u \in 0..N-1 :
       /\ pc[u] \in {"broadcast", "nobroadcast"}
       /\ recv[u] = {}
  /\ sent = {}

Receive(u) ==
  /\ pc[u] # "accepted"
  /\ recv' = [recv EXCEPT ![u] = recv[u] \cup
                {m \in sent : m.snd \in correct /\ m.tp = "ech"}]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* A correct process that got the INIT message accepts immediately and
\* sends its own ECHO downstream to every other process.
BroadcastInit(u) ==
  /\ pc[u] = "broadcast"
  /\ pc' = [pc EXCEPT ![u] = "sent"]
  /\ sent' = sent \cup {[snd |-> u, tp |-> "ech"]}
  /\ UNCHANGED << correct, faulty, recv >>

\* Below N-2T ECHO messages the process waits for more; it now sends its
\* own ECHO without yet accepting (it is still below the accept threshold).
RelayBeforeAccept(u) ==
  /\ pc[u] = "nosend"
  /\ Cardinality(Echoes(u) \cap correct) >= N - 2 * T
  /\ Cardinality(Echoes(u) \cap correct) < N - T
  /\ pc' = [pc EXCEPT ![u] = "sent"]
  /\ sent' = sent \cup {[snd |-> u, tp |-> "ech"]}
  /\ UNCHANGED << correct, faulty, recv >>

\* At or above the accept threshold the process sends its ECHO and accepts.
RelayedAccept(u) ==
  /\ pc[u] = "nosend"
  /\ Cardinality(Echoes(u) \cap correct) >= N - T
  /\ pc' = [pc EXCEPT ![u] = "accepted"]
  /\ sent' = sent \cup {[snd |-> u, tp |-> "ech"]}
  /\ UNCHANGED << correct, faulty, recv >>

\* A process that already broadcast its own ECHO may still be waiting on
\* a sufficient quorum of inbound ECHOs before it is allowed to accept.
RelayAccept(u) ==
  /\ pc[u] = "sent"
  /\ Cardinality(Echoes(u) \cap correct) >= N - T
  /\ pc' = [pc EXCEPT ![u] = "accepted"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

AcceptAny == \E u \in 0..N-1 : RelayedAccept(u) \/ RelayAccept(u)
RelayAny == \E u \in 0..N-1 : RelayBeforeAccept(u) \/ BroadcastInit(u)

Next ==
  \/ AcceptAny
  \/ RelayAny
  \/ \E u \in 0..N-1 : Receive(u)

Spec == Init /\ [][Next]_vars /\ WF_vars(Receive(0)) /\ WF_vars(Receive(1))
        /\ WF_vars(Receive(2)) /\ WF_vars(Receive(3))
        /\ WF_vars(AcceptAny) /\ WF_vars(RelayAny)

CorrLtl == \A u \in correct : pc[u] = "broadcast" ~> (pc[u] = "accepted")
RelayLtl == (\E u \in correct : pc[u] = "sent") ~> (\A u \in correct : pc[u] = "accepted")
UnforgLtl == (\A u \in correct : pc[u] = "nobroadcast") ~> (\A u \in correct : pc[u] # "accepted")

====
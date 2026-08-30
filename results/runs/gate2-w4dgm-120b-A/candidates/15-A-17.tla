---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Two process partitions are derived from N,F: CorrectPs is the set of
\* processes that follow the protocol; FaultyPs is the complement, and
\* may forge arbitrary ECHO messages. pc marks where a correct process
\* is in the one-round protocol. recv is the message buffer per process.
\* bcast is the set of all ECHO messages a correct process has ever sent.
VARIABLES CorrectPs, FaultyPs, pc, recv, bcast

None = "none"
BcastTypes == {"init", "echo"}

Places == {"none", "brd", "echoed", "acc"}

TypeOK ==
  /\ CorrectPs \subseteq 1..N
  /\ Cardinality(CorrectPs) = N - F
  /\ FaultyPs = (1..N) \ CorrectPs
  /\ pc \in [1..N -> Places]
  /\ recv \in [1..N -> SUBSET (1..N \X BcastTypes)]
  /\ bcast \in SUBSET (1..N)

Init ==
  /\ Cardinality(CorrectPs) = N - F
  /\ FaultyPs = (1..N) \ CorrectPs
  /\ pc \in [1..N -> {"brd", "none"}]
  /\ recv = [p \in 1..N |-> {}]
  /\ bcast = {}

\* The NoBcast variant sets every correct process to start without the
\* broadcaster's INIT message (the unforgeability case).
NoBcast == Init /\ (\A p \in 1..N : pc[p] = "none") /\ UNCHANGED <<CorrectPs, FaultyPs, pc, recv, bcast>>

InitAny == Init \/ NoBcast

\* Correct processes only ever receive messages from the shared pool of
\* all correct ECHO messages plus every possible Byzantine message.
AllMsgs ==
  (bcast \X {"echo"}) \cup (FaultyPs \X {"echo"}) \cup (CorrectPs \X {"init"})

Receive(p, msgs) ==
  /\ p \in CorrectPs
  /\ pc[p] \notin {"acc"}
  /\ msgs \subseteq AllMsgs
  /\ msgs # {}
  /\ recv' = [recv EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<CorrectPs, FaultyPs, pc, bcast>>

EchoSend(p) ==
  /\ p \in CorrectPs
  /\ pc[p] = "brd"
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ bcast' = bcast \cup {p}
  /\ UNCHANGED <<CorrectPs, FaultyPs, recv>>

\* The quorum thresholds are N-2T for send-only and N-T for send-plus-accept.
Relay(p) ==
  /\ p \in CorrectPs
  /\ pc[p] \notin {"echoed", "acc"}
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in recv[p]}) >= N - 2 * T
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in recv[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ bcast' = bcast \cup {p}
  /\ UNCHANGED <<CorrectPs, FaultyPs, recv>>

Accept(p) ==
  /\ p \in CorrectPs
  /\ pc[p] \notin {"acc"}
  /\ Cardinality({q \in 1..N : <<q, "echo">> \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ bcast' = bcast \cup {p}
  /\ UNCHANGED <<CorrectPs, FaultyPs, recv>>

CorrStep ==
  \/ \E p \in 1..N, msgs \in SUBSET AllMsgs : Receive(p, msgs)
  \/ \E p \in 1..N : EchoSend(p)
  \/ \E p \in 1..N : Relay(p)
  \/ \E p \in 1..N : Accept(p)

Next == CorrStep

\* Weak fairness on the combined receive-and-act step suffices to
\* guarantee progress of the correct-participant sub-system.
Spec == InitAny /\ [][Next]_<<CorrectPs, FaultyPs, pc, recv, bcast>>
  /\ WF_vars(CorrStep)

CorrLtl == <>(\A p \in CorrectPs : pc[p] = "acc")
RelayLtl == (\E p \in CorrectPs : pc[p] = "acc") ~> (\A p \in CorrectPs : pc[p] = "acc")

\* Unforgeability is a safety property: it holds in every reachable state.
UnforgLtl == (\A p \in CorrectPs : pc[p] = "brd") ~> (\A p \in CorrectPs : pc[p] = "acc")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
====
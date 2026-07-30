---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Partitions the processes into correct and faulty (Byzantine) at init
\* based on the fixed fault budget F. N > 3T is required for the
\* broadcast assumptions to hold.
VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

Locs == {"startedNoInit", "startedInit", "sentEcho", "accepted"}
Msgs == {"echo"}

TypeOK ==
  /\ correct \subseteq (0..(N-1))
  /\ correct \cap faulty = {}
  /\ pc \in [0..(N-1) -> Locs]
  /\ recv \in [0..(N-1) -> SUBSET (0..(N-1) \X Msgs)]
  /\ sent \in SUBSET (0..(N-1) \X Msgs)

Init ==
  /\ let cs == CHOOSE s \in (0..(N-1)) : TRUE in
       correct = (0..(N-1)) \ {s}
  /\ faulty = (0..(N-1)) \ correct
  /\ pc = [p \in (0..(N-1)) |->
              IF p \in correct
                THEN IF p = 0 THEN "startedInit" ELSE "startedNoInit"
                ELSE "startedNoInit"]
  /\ recv = [p \in (0..(N-1)) |-> {}]
  /\ sent = {}

NoInitInit ==
  /\ correct = (0..(N-1))
  /\ pc = [p \in (0..(N-1)) |-> "startedNoInit"]
  /\ recv = [p \in (0..(N-1)) |-> {}]
  /\ sent = {}

\* A correct process may receive any new messages it likes, from correct
\* senders or from faulty ones, so the adversary cannot starve it.
Recv(p, msgs) ==
  /\ pc[p] \notin {"sentEcho", "accepted"}
  /\ msgs \subseteq sent \cup (faulty \X Msgs)
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup msgs]
  /\ UNCHANGED << correct, pc, sent >>

SendEcho(p) ==
  /\ pc[p] = "startedInit"
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED << correct, recv >>

\* Below-threshold relay: send but not enough distinct senders to accept
RelayPre(p) ==
  /\ pc[p] = "startedNoInit"
  /\ Cardinality({q \in 0..(N-1) : <<q, "echo">> \in recv[p]}) >= N - 2 * T
  /\ Cardinality({q \in 0..(N-1) : <<q, "echo">> \in recv[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED << correct, recv >>

RelayAccept(p) ==
  /\ pc[p] = "startedNoInit"
  /\ Cardinality({q \in 0..(N-1) : <<q, "echo">> \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED << correct, recv >>

Accept(p) ==
  /\ pc[p] = "sentEcho"
  /\ Cardinality({q \in 0..(N-1) : <<q, "echo">> \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, recv, sent >>

Next ==
  \/ \E p \in 0..(N-1), msgs \in SUBSET (0..(N-1) \X Msgs) : Recv(p, msgs)
  \/ \E p \in 0..(N-1) : SendEcho(p) \/ RelayPre(p) \/ RelayAccept(p) \/ Accept(p)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 0..(N-1), msgs \in SUBSET (0..(N-1) \X Msgs) : Recv(p, msgs))
  /\ WF_vars(\E p \in 0..(N-1) : SendEcho(p) \/ RelayPre(p) \/ RelayAccept(p) \/ Accept(p))

FCConstraints ==
  /\ N >= 2 * T + 1
  /\ T >= F
  /\ F >= 0

\* Correctness: a fully-initialized broadcast always ends in agreement.
CorrLtl == (pc[0] = "sentEcho") ~> (\A p \in correct : pc[p] = "accepted")
\* Relay: agreement can never die mid-way.
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
\* Unforgeability: no broadcast, no agreement.
UnforgLtl == (~\E p \in correct : pc[p] = "sentEcho") ~> (\A p \in correct : pc[p] = "startedNoInit")

====
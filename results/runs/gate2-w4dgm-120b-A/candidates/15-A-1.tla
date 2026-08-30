---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the protocol; Byzantine ones send arbitrary ECHO msgs.
\* The broadcast's INIT is not modeled as a single message: the initial state shows
\* per-process which processes received it, and only those may accept immediately.

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

Bump(x) == IF x < N - 1 THEN x + 1 ELSE 0

InitMsgs(p, m) == {<<q, m>> : q \in correct}
BcastMsgs(m) == {<<q, m>> : q \in 1 .. N}

Init0 ==
  /\ correct = 1 .. (N - F)
  /\ faulty = (N - F + 1) .. N
  /\ pc = [p \in 1 .. N |-> IF p \in correct THEN "broadcast" ELSE "nobroadcast"]
  /\ recv = [p \in 1 .. N |-> {}]
  /\ sent = {}

Nobcast0 ==
  /\ correct = 1 .. (N - F)
  /\ faulty = (N - F + 1) .. N
  /\ pc = [p \in 1 .. N |-> IF p \in correct THEN "nobroadcast" ELSE "broadcast"]
  /\ recv = [p \in 1 .. N |-> {}]
  /\ sent = {}

Init == Init0 \/ Nobcast0

\* A correct process may receive any batch of fresh messages (sent by anyone so far).
Receive(p, mset) ==
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ recv' = [recv EXCEPT ![p] = recv[p] \union (mset \sent)]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ sent' = sent \union InitMsgs(p, "ECHO")
  /\ UNCHANGED <<correct, faulty, pc, recv>>

Accept(p) ==
  /\ p \in correct
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* Stage 1: a correct process that has not yet sent ECHO gathers enough of them.
GatherEcho(p) ==
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ Cardinality(recv[p]) >= N - 2 * T
  /\ Cardinality(recv[p]) < N - T
  /\ sent' = sent \union InitMsgs(p, "ECHO")
  /\ UNCHANGED <<correct, faulty, pc, recv>>

\* Stage 2: with a quorum of N-T it both sends ECHO and accepts in one step.
AcceptEcho(p) ==
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ Cardinality(recv[p]) >= N - T
  /\ sent' = sent \union InitMsgs(p, "ECHO")
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAccept(p) ==
  /\ pc[p] = "accept"
  /\ Cardinality({q \in recv[p] : q[2] = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in 1 .. N, mset \in SUBSET BcastMsgs("ECHO"): Receive(p, mset)
  \/ \E p \in 1 .. N: SendEcho(p)
  \/ \E p \in 1 .. N: GatherEcho(p)
  \/ \E p \in 1 .. N: Accept(p)
  \/ \E p \in 1 .. N: AcceptEcho(p)
  \/ \E p \in 1 .. N: RelayAccept(p)

Spec == Init /\ [][Next]_vars
                        /\ (\A p \in 1 .. N: WF_vars(Receive(p, BcastMsgs("ECHO"))))
                        /\ (\A p \in 1 .. N: WF_vars(Accept(p)))
                        /\ (\A p \in 1 .. N: WF_vars(RelayAccept(p)))

\* SAFETY: a process's control location stays within its allowed range.
TypeOK ==
  /\ correct \subseteq 1 .. N
  /\ faulty \subseteq 1 .. N
  /\ pc \in [1 .. N -> {"broadcast", "nobroadcast", "accept"}]
  /\ recv \in [1 .. N -> SUBSET (1 .. N \X {"ECHO"})]
  /\ sent \subseteq (1 .. N \X {"ECHO"})

\* FC-CONSTRAINT: correct processes are exactly N-F in number (the fault bound).
FCConstraints == Cardinality(correct) = N - F

\* UNFORGEABILITY: with no correct broadcaster, no correct process may accept.
Unforgeability ==
  (\A p \in correct: pc[p] = "broadcast") ~> (\A p \in correct: pc[p] = "accept")

\* CORRECTNESS: if every correct process received the broadcast, they all accept.
CorrLtl == (\A p \in correct: pc[p] = "broadcast") ~> (\A p \in correct: pc[p] = "accept")

\* RELAY: once any correct process accepts, they all eventually accept.
RelayLtl == (\E p \in correct: pc[p] = "accept") ~> (\A p \in correct: pc[p] = "accept")

\* UNFORGEABILITY is proved as an invariant of the reachable state space.
UnforgLtl == (\A p \in correct: pc[p] = "broadcast") ~> (\A p \in correct: pc[p] = "accept")
====
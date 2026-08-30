---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* The "init broadcast" is encoded as an initial program counter value per
\* process instead of a dedicated broadcaster; a process already has it iff
\* it received the one-round broadcast message.
\* Unforgeability is the safety property that a run with no such initial
\* receipt never leads to acceptance by a correct process.
\* CorrLtl and RelayLtl are the two liveness properties.

VARIABLES correct, faulty, pc, recv, sent

\* pc: control location per correct process: "nosend" (no INIT), "init"
\* (received the INIT broadcast), "sent" (sent ECHO), "accepted" (delivered).
\* recv: set of (sender,kind) messages each correct process has received.
\* sent: set of (sender,kind) messages actually emitted by correct processes.
Vars == << correct, faulty, pc, recv, sent >>

RECURSIVE MsgsFrom(_, _)
MsgsFrom(set, k) ==
  IF set = {} THEN {}
  ELSE LET p == CHOOSE x \in set : TRUE IN
       {<<p, k>>} \cup MsgsFrom(set \ {p}, k)

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ pc \in [1..N -> {"nosend", "init", "sent", "accepted"}]
  /\ recv \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sent \subseteq (1..N \X {"echo"})

Init ==
  \E initLoc \in {"nosend", "init"}:
    /\ correct = {p \in 1..N : p <= N - F}
    /\ faulty = {p \in 1..N : p > N - F}
    /\ pc = [p \in 1..N |-> IF p \in correct THEN initLoc ELSE "nosend"]
    /\ sent = {}
    /\ recv = [p \in 1..N |-> {}]

\* A correct process may receive any subset of all messages that correct
\* senders could have emitted together with arbitrary Byzantine ones.
ReceiveMsgs(p, m) ==
  /\ p \in correct
  /\ pc[p] \notin {"accepted"}
  /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "init" THEN "sent" ELSE pc[p]]
  /\ recv' = [recv EXCEPT ![p] = m]
  /\ UNCHANGED <<correct, faulty, sent>>

\* A correct process that has received the one-round broadcast accepts
\* immediately (it is the sole source of trust in the system) and sends ECHO.
BroadcastAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* With only a quorum short of the full threshold, ECHO is emitted but stop
\* short of accepting -- this is the "relay only" intermediate state.
Relay(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"sent", "accepted"}
  /\ Cardinality(recv[p]) >= N - 2 * T
  /\ Cardinality(recv[p]) < N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptThreshold(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"accepted"}
  /\ Cardinality(recv[p]) >= N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAccept(p) == Relay(p) \/ AcceptThreshold(p)

Next ==
  \/ \E p \in 1..N, m \in SUBSET (1..N \X {"echo"}) : ReceiveMsgs(p, m)
  \/ \E p \in 1..N : BroadcastAccept(p) \/ RelayAccept(p)

\* Safety: unforgeability of the acceptance step, and pure domain type safety.
UnforgLtl == (\A p \in 1..N : pc[p] = "init") ~> (\A p \in 1..N : pc[p] = "accepted")
FCConstraints == \A p \in 1..N : p \in correct => pc[p] \in {"nosend", "init", "sent", "accepted"}

Spec == Init /\ [][Next]_Vars /\ WF_Vars(\E p \in 1..N : RelayAccept(p))

CorrLtl == (\A p \in 1..N : pc[p] = "init") ~> (\A p \in 1..N : pc[p] = "accepted")
RelayLtl == (\E p \in 1..N : pc[p] = "accepted") ~> (\A p \in 1..N : pc[p] = "accepted")

====
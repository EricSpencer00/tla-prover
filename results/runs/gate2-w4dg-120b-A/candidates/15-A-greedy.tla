---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the protocol; faulty ones may send arbitrary ECHO
\* messages. The control location is a program counter per process.
VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Locs == {"init", "noinit", "echoed", "accepted"}
Msgs == {"ECHO"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Locs]
  /\ recv \in [1..N -> SUBSET (1..N \X Msgs)]
  /\ sent \subseteq (1..N \X Msgs)

\* No forged messages: a correct process only ever receives messages that a
\* correct sender actually sent, plus whatever Byzantine processes may send.
FCConstraints ==
  \A p \in 1..N : recv[p] \subseteq (sent \cup (faulty \X Msgs))

Init ==
  /\ correct = {1, 2, 3}
  /\ faulty = {4}
  /\ pc = [p \in 1..N |-> IF p <= 3 THEN "init" ELSE "noinit"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A restricted initial state where no correct process received the broadcast.
InitNoBroadcast ==
  /\ correct = {1, 2, 3}
  /\ faulty = {4}
  /\ pc = [p \in 1..N |-> "noinit"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives a set of new messages (from correct senders and
\* from Byzantine processes, which may be arbitrary).
Receive(p, m) ==
  /\ pc[p] \in {"init", "noinit"}
  /\ m \subseteq (sent \cup (faulty \X Msgs))
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that received the broadcast immediately accepts and sends
\* an ECHO to all.
BroadcastAccept(p) ==
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to send its own, but not enough to accept yet.
Relay(p) ==
  /\ pc[p] \in {"init", "noinit"}
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recv[p]}) >= N - 2 * T
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recv[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to both send its own and accept.
RelayAccept(p) ==
  /\ pc[p] \in {"init", "noinit"}
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has already sent ECHO receives enough ECHO messages
\* to accept.
Accept(p) ==
  /\ pc[p] = "echoed"
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in 1..N, m \in SUBSET (1..N \X Msgs) : Receive(p, m)
  \/ \E p \in 1..N : BroadcastAccept(p)
  \/ \E p \in 1..N : Relay(p)
  \/ \E p \in 1..N : RelayAccept(p)
  \/ \E p \in 1..N : Accept(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, m \in SUBSET (1..N \X Msgs) : Receive(p, m))
  /\ WF_vars(\E p \in 1..N : BroadcastAccept(p))
  /\ WF_vars(\E p \in 1..N : Relay(p))
  /\ WF_vars(\E p \in 1..N : RelayAccept(p))
  /\ WF_vars(\E p \in 1..N : Accept(p))

\* Unforgeability: if no correct process broadcasts, no correct process accepts.
UnforgLtl == (\A p \in correct : pc[p] = "noinit") ~> (\A p \in correct : pc[p] = "accepted")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accepted")

RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

====
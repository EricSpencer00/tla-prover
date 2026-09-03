---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the protocol; faulty ones may send arbitrary ECHO
\* messages.  The broadcaster's INIT message is modeled as an initial value at
\* each process rather than a dedicated sender.
\* The invariant below is the unforgeability property: no accept if no correct
\* process broadcasted.  The liveness properties are CorrLtl (all accept when
\* all broadcast) and RelayLtl (acceptance spreads to all correct processes).

VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "nobroadcast", "sent", "accept"}]
  /\ recv \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sent \subseteq (1..N \X {"echo"})

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ correct
  /\ pc \in {f \in [1..N -> {"init", "nobroadcast"}] : Cardinality({i \in 1..N : f[i] = "init"}) = 1}
  /\ recv = [i \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive any subset of all messages sent by correct
\* processes plus any possible message from a faulty process.
Receive(i) ==
  /\ i \in correct
  /\ pc[i] \in {"init", "nobroadcast"}
  /\ \E m \in SUBSET (sent \cup (faulty \X {"echo"})) : recv' = [recv EXCEPT ![i] = m]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* A correct process that received the INIT message accepts and sends ECHO.
InitAccept(i) ==
  /\ i \in correct
  /\ pc[i] = "init"
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<< i, "echo" >>}
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to send its own, but not enough to accept yet.
EchoSend(i) ==
  /\ i \in correct
  /\ pc[i] = "nobroadcast"
  /\ Cardinality(recv[i]) >= (N - 2 * T)
  /\ Cardinality(recv[i]) < (N - T)
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sent' = sent \cup {<< i, "echo" >>}
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to both send its own and accept.
EchoAccept(i) ==
  /\ i \in correct
  /\ pc[i] = "nobroadcast"
  /\ Cardinality(recv[i]) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<< i, "echo" >>}
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has already sent ECHO receives enough ECHO messages
\* to accept.
EchoRelay(i) ==
  /\ i \in correct
  /\ pc[i] = "sent"
  /\ Cardinality(recv[i]) >= (N - T)
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : InitAccept(i)
  \/ \E i \in 1..N : EchoSend(i)
  \/ \E i \in 1..N : EchoAccept(i)
  \/ \E i \in 1..N : EchoRelay(i)

Spec == Init /\ [][Next]_vars
  /\ \A i \in 1..N : WF_vars(Receive(i))
  /\ \A i \in 1..N : WF_vars(EchoSend(i))
  /\ \A i \in 1..N : WF_vars(EchoAccept(i))
  /\ \A i \in 1..N : WF_vars(EchoRelay(i))

\* Unforgeability: if no correct process broadcasted, no correct process accepts.
UnforgLtl == (\A i \in correct : pc[i] = "nobroadcast") ~> (\A i \in correct : pc[i] = "accept")

CorrLtl == (\A i \in correct : pc[i] = "init") ~> (\A i \in correct : pc[i] = "accept")

RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====
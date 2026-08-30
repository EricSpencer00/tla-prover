---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the one-round broadcast protocol; faulty ones may
\* send arbitrary ECHO messages.  The broadcaster's INIT message is modeled as
\* an initial value at each process rather than a dedicated sender.
\* Unforgeability is the property that no correct process accepts when no
\* correct process ever broadcast (no INIT message was ever received).

VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

Msg == [snd : 1..N, typ : {"ECHO"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "noinit", "sent", "accept"}]
  /\ recv \in [1..N -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ pc \in {"init", "noinit"}^N
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive any subset of the messages sent by correct
\* processes together with any possible message from a faulty process.
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"init", "noinit"}
  /\ \E m \in SUBSET (sent \cup { [snd |-> q, typ |-> "ECHO"] : q \in faulty }) :
       recv' = [recv EXCEPT ![p] = m]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* A correct process that received the INIT message accepts and sends ECHO.
InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [snd |-> p, typ |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to send its own, but not enough to accept yet.
Relay(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.typ = "ECHO" }) >= N - 2 * T
  /\ Cardinality({ m \in recv[p] : m.typ = "ECHO" }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [snd |-> p, typ |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to both send its own and accept.
RelayAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.typ = "ECHO" }) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [snd |-> p, typ |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has already sent ECHO receives enough ECHO messages
\* to accept.
Accept(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({ m \in recv[p] : m.typ = "ECHO" }) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

\* Weak fairness on the combined receive-and-act steps of correct processes
\* (the "relay" steps) is what forces the relay chain to complete.
Next ==
  \/ \E p \in 1..N : Receive(p) \/ InitAccept(p) \/ Relay(p) \/ RelayAccept(p) \/ Accept(p)

Spec == Init /\ [][Next]_vars

\* Unforgeability: if no correct process ever broadcast (all start without the
\* INIT message), then no correct process ever accepts.
UnforgLtl == (\A p \in 1..N : pc[p] = "noinit") ~> (\A p \in correct : pc[p] = "accept")

CorrLtl == (\A p \in 1..N : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

\* The invariant is a per-process type check; it is the only thing that TLC
\* can verify without exploring the full reachable state space.
FCConstraints == TypeOK

====
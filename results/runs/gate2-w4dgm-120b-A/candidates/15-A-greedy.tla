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

Msg == [sender : 1..N, kind : {"ECHO"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "noinit", "sent", "accept"}]
  /\ recv \in [1..N -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ pc \in {"init", "noinit"}^N
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive any subset of the messages sent by correct
\* processes plus any possible message from a faulty process.
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"init", "noinit"}
  /\ \E m \in SUBSET (sent \cup { [sender |-> q, kind |-> "ECHO"] : q \in faulty }) :
       recv' = [recv EXCEPT ![p] = m]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* A correct process that received the INIT message accepts and sends ECHO.
InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to send its own, but not enough to accept yet.
EchoSend(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - 2 * T)
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to both send its own and accept.
EchoAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has already sent ECHO receives enough ECHO messages
\* to accept.
EchoAcceptLater(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : InitAccept(p)
  \/ \E p \in 1..N : EchoSend(p)
  \/ \E p \in 1..N : EchoAccept(p)
  \/ \E p \in 1..N : EchoAcceptLater(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(Receive(p))
  /\ \A p \in 1..N : WF_vars(InitAccept(p))
  /\ \A p \in 1..N : WF_vars(EchoSend(p))
  /\ \A p \in 1..N : WF_vars(EchoAccept(p))
  /\ \A p \in 1..N : WF_vars(EchoAcceptLater(p))

\* Unforgeability: if no correct process ever broadcast (no INIT message was
\* ever received), no correct process ever accepts.
UnforgLtl == (\A p \in correct : pc[p] # "init") ~> (\A p \in correct : pc[p] = "accept")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = (1..N)

====
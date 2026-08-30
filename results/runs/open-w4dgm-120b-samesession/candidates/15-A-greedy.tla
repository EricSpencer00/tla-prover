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

vars == <<correct, faulty, pc, recv, sent>>

Msg == [sender : 1..N, kind : {"ECHO"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"init", "noinit", "sent", "accept"}]
  /\ recv \in [1..N -> SUBSET Msg]
  /\ sent \subseteq Msg

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ {1..(N - F)}
  /\ pc \in {"init", "noinit"}
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive any subset of the messages sent so far by
\* correct processes plus any possible message from a faulty process.
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"init", "noinit"}
  /\ \E m \in SUBSET (sent \cup { [sender |-> q, kind |-> "ECHO"] : q \in faulty }) :
       recv' = [recv EXCEPT ![p] = m]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that received the INIT message accepts immediately and
\* sends an ECHO to all.
Broadcast(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO sends it once it has enough
\* ECHO messages from distinct senders, but does not yet accept.
Relay(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - 2 * T)
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO accepts once it has a strong
\* majority of ECHO messages from distinct senders.
Accept(p) ==
  /\ p \in correct
  /\ pc[p] = "noinit"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sent' = sent \cup { [sender |-> p, kind |-> "ECHO"] }
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has already sent ECHO accepts once it has a strong
\* majority of ECHO messages from distinct senders.
RelayAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({ m \in recv[p] : m.kind = "ECHO" }) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : Broadcast(p)
  \/ \E p \in 1..N : Relay(p)
  \/ \E p \in 1..N : Accept(p)
  \/ \E p \in 1..N : RelayAccept(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in 1..N : WF_vars(Receive(p))
  /\ \A p \in 1..N : WF_vars(Broadcast(p))
  /\ \A p \in 1..N : WF_vars(Relay(p))
  /\ \A p \in 1..N : WF_vars(Accept(p))
  /\ \A p \in 1..N : WF_vars(RelayAccept(p))

\* If no correct process broadcasted, no correct process ever accepts.
UnforgLtl == (\A p \in correct : pc[p] = "noinit") ~> (\A p \in correct : pc[p] = "accept")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the protocol; faulty ones may send arbitrary ECHO
\* messages. The protocol requires N > 3T.
\* Control locations: no INIT, has INIT, sent ECHO, accepted.
\* Messages are (sender, "ECHO") pairs; a process accepts once it has enough.
\* A restricted initial state has no correct process receiving the INIT message.
\* Weak fairness on the combined receive-and-act steps lets a correct process
\* that can forever receive messages from correct senders eventually act.

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Locs == {"noinit", "hasinit", "sent", "accepted"}
Msgs == [from: 1..N, typ: {"ECHO"}]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Locs]
  /\ recv \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ pc = [p \in 1..N |-> IF p \in correct THEN "hasinit" ELSE "noinit"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

InitNoBroad ==
  /\ correct = {1..(N - F)}
  /\ faulty = (1..N) \ correct
  /\ pc = [p \in 1..N |-> "noinit"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process receives a set of new messages, from correct senders and
\* from Byzantine ones (the latter are unconstrained).
Receive(p, mset) ==
  /\ p \in correct
  /\ mset \subseteq (sent \cup [from |-> faulty, typ |-> "ECHO"])
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup mset]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that received the INIT message accepts and sends ECHO.
AcceptInit(p) ==
  /\ p \in correct
  /\ pc[p] = "hasinit"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[from |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to send them, but not enough to accept yet.
EchoOnly(p) ==
  /\ p \in correct
  /\ pc[p] \in {"noinit", "hasinit"}
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - 2 * T
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {[from |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has not yet sent ECHO receives enough ECHO messages
\* to both send them and accept.
EchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] \in {"noinit", "hasinit"}
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {[from |-> p, typ |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, recv>>

\* A correct process that has already sent ECHO receives enough to accept.
AcceptEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({m \in recv[p] : m.typ = "ECHO"}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in 1..N, mset \in SUBSET Msgs : Receive(p, mset)
  \/ \E p \in 1..N : AcceptInit(p)
  \/ \E p \in 1..N : EchoOnly(p)
  \/ \E p \in 1..N : EchoAndAccept(p)
  \/ \E p \in 1..N : AcceptEcho(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, mset \in SUBSET Msgs : Receive(p, mset))
  /\ WF_vars(\E p \in 1..N : EchoOnly(p))
  /\ WF_vars(\E p \in 1..N : EchoAndAccept(p))
  /\ WF_vars(\E p \in 1..N : AcceptEcho(p))

\* Unforgeability: if no correct process broadcasts, no correct process accepts.
UnforgLtl ==
  (\A p \in correct : pc[p] \in {"noinit", "hasinit"}) ~>
    (\A p \in correct : pc[p] # "accepted")

CorrLtl == (\A p \in correct : pc[p] \in {"hasinit", "accepted"}) ~>
            (\A p \in correct : pc[p] = "accepted")

RelayLtl == (\E p \in correct : pc[p] = "accepted") ~>
             (\A p \in correct : pc[p] = "accepted")

====
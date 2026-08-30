---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

Controls == {"none", "initRecv", "sentEcho", "accept"}

\* The broadcaster's INIT message is represented by a per-process start flag
\* rather than a dedicated sender: a process that received INIT may accept
\* immediately, without any ECHO, so the broadcast is not the sole path.
InitRecv == { p \in 1..N : pc[p] = "initRecv" }

Nodes == 1..N
MsgTypes == {"echo"}
Msgs == Nodes \X MsgTypes
Senders(m) == { m[1] }

TypeOK ==
  /\ correct \subseteq Nodes
  /\ Cardinality(correct) = N - F
  /\ faulty = Nodes \ correct
  /\ pc \in [Nodes -> Controls]
  /\ inbox \in [Nodes -> SUBSET Msgs]
  /\ sent \subseteq Msgs

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = Nodes \ correct
  /\ pc \in [Nodes -> {"initRecv", "none"}]
  /\ inbox = [p \in Nodes |-> {}]
  /\ sent = {}

\* The restricted "no broadcast" initial state: all correct processes start
\* without having received the broadcaster's INIT message.
InitNoBroad ==
  /\ Init
  /\ \A p \in correct : pc[p] = "none"

CorrectSent == { <<p, "echo">> : p \in correct }

\* Reception is nondeterministic over everything correct processes ever sent and
\* everything a Byzantine process could have fabricated.
Receive(p, msgs) ==
  /\ pc[p] \in {"initRecv", "none"}
  /\ msgs \subseteq (CorrectSent \cup (faulty \X {"echo"}))
  /\ inbox' = [inbox EXCEPT ![p] = @ \cup msgs]
  /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "none" THEN "initRecv" ELSE @]
  /\ UNCHANGED <<correct, faulty, sent>>

\* A correct process that received INIT may accept without any ECHO at all.
AcceptFromInit(p) ==
  /\ pc[p] = "initRecv"
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox>>

SendEcho(p) ==
  /\ pc[p] = "none"
  /\ Cardinality(Senders(inbox[p])) >= N - 2 * T
  /\ Cardinality(Senders(inbox[p])) < N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ UNCHANGED <<correct, faulty, inbox>>

AcceptAfterEcho(p) ==
  /\ pc[p] = "none"
  /\ Cardinality(Senders(inbox[p])) >= N - T
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox>>

AcceptLater(p) ==
  /\ pc[p] = "sentEcho"
  /\ Cardinality(Senders(inbox[p])) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

\* Receive-and-act is strongly fair for each correct process: it keeps
\* delivering messages and reacting to them until it has accepted.
Next ==
  \/ \E p \in correct, msgs \in SUBSET Msgs : Receive(p, msgs)
  \/ \E p \in correct : AcceptFromInit(p) \/ SendEcho(p) \/ AcceptAfterEcho(p) \/ AcceptLater(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in correct :
             /\ TRUE
             /\ SF_vars(\E msgs \in SUBSET Msgs : Receive(p, msgs))
             /\ SF_vars(AcceptFromInit(p))
             /\ SF_vars(SendEcho(p))
             /\ SF_vars(AcceptAfterEcho(p))
             /\ SF_vars(AcceptLater(p))

\* Unforgeability: if no correct process ever broadcast (no INIT received),
\* then no correct process ever accepts.
UnforgLtl == (InitRecv = {}) ~> (InitRecv = {} /\ \A p \in correct : pc[p] = "accept")

CorrLtl == (\A p \in correct : pc[p] = "initRecv") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====
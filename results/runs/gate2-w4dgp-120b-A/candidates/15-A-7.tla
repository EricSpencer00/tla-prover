---- MODULE bcastByz ----
\* Reliable broadcast with Byzantine faults: a correct process accepts once it has
\* collected a quorum of ECHO messages from distinct senders. Faulty processes
\* may send arbitrary ECHO messages (the "malicious" parameter). When no
\* correct process broadcasts, no correct process should ever accept.
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Processes == 1..N
Msgs == {"ECHO"}
NoEcho == "none"

VARIABLES correct, senders, pc, recv, sent
vars == <<correct, senders, pc, recv, sent>>

\* Quorum predicates: N-2T justifies sending an ECHO; N-T justifies accepting.
\* senderSet(m, r) = the set of distinct senders of message m received by r.
senderSet(m, r) == {x \in Processed(r) : m \in recv[r][x]}
Processed(r) == {x \in Processes : pc[x] # NoEcho}

TypeOK ==
  /\ correct \subseteq Processes
  /\ Cardinality(correct) = N - F
  /\ senders \in [Process] {1, 2}
  /\ pc \in [Processes -> {0, 1, 2}]
  /\ recv \in [Processes -> [Processes -> SUBSET Msgs]]
  /\ sent \subseteq (Processes \X Msgs)

\* Safety: if no correct process broadcasts (all start in the non-broadcast
\* state), no correct process ever accepts.
FCConstraints == \A r \in correct : pc[r] = 0

Init ==
  /\ correct \subseteq Processes
  /\ Cardinality(correct) = N - F
  /\ senders \in [Process -> {1, 2}]
  /\ pc = [r \in Processes |-> IF senders[r] = 1 THEN 1 ELSE 0]
  /\ recv = [r \in Processes |-> [x \in Processes |-> {}]]
  /\ sent = {}

\* A correct process receives a set of new messages: all of its own sent messages
\* plus all possible messages from Byzantine processes, nondeterministically.
Receive(r) ==
  /\ r \in correct
  /\ pc[r] # 2
  /\ \E m \in [Processes -> SUBSET Msgs] :
       /\ m \in sent
       /\ recv' = [recv EXCEPT ![r] = recv[r] \cup m]
  /\ UNCHANGED <<correct, senders, pc, sent>>

\* A process that received the broadcaster's INIT immediately accepts and sends
\* an ECHO to all.
ActOnInit(r) ==
  /\ r \in correct
  /\ pc[r] = 1
  /\ pc' = [pc EXCEPT ![r] = 2]
  /\ sent' = sent \cup {<<r, "ECHO">>}
  /\ UNCHANGED <<correct, senders, recv>>

\* A process that has not yet sent an ECHO gathers a quorum of N-2T distinct
\* ECHOs and sends one, but has not yet accepted.
SendEchoWeak(r) ==
  /\ r \in correct
  /\ pc[r] = 0
  /\ Cardinality(senderSet("ECHO", r)) >= N - 2 * T
  /\ Cardinality(senderSet("ECHO", r)) < N - T
  /\ pc' = [pc EXCEPT ![r] = 2]
  /\ sent' = sent \cup {<<r, "ECHO">>}
  /\ UNCHANGED <<correct, senders, recv>>

\* With a stronger quorum of N-T distinct ECHOs a process both sends and accepts.
SendEchoStrong(r) ==
  /\ r \in correct
  /\ pc[r] = 0
  /\ Cardinality(senderSet("ECHO", r)) >= N - T
  /\ pc' = [pc EXCEPT ![r] = 2]
  /\ sent' = sent \cup {<<r, "ECHO">>}
  /\ UNCHANGED <<correct, senders, recv>>

\* A process that already sent an ECHO accepts once it collects N-T distinct
\* ECHOs.
Accept(r) ==
  /\ r \in correct
  /\ pc[r] = 2
  /\ Cardinality(senderSet("ECHO", r)) >= N - T
  /\ \A x \in Processes : recv' = [recv EXCEPT ![r][x] = recv[r][x]]
  /\ UNCHANGED <<correct, senders, pc, sent>>

Next ==
  \/ \E r \in Processes : Receive(r) \/ ActOnInit(r) \/ SendEchoWeak(r) \/ SendEchoStrong(r) \/ Accept(r)

\* Fairness: any correct process that can forever receive messages from correct
\* senders and act on them eventually does (necessary for liveness).
Spec ==
  /\ Init /\ [][Next]_vars
  /\ \A r \in correct :
       WF_vars(Receive(r) \/ ActOnInit(r) \/ SendEchoWeak(r) \/ SendEchoStrong(r) \/ Accept(r))

\* With no broadcast, no correct process ever accepts.
UnforgLtl == (senders = [r \in Process |-> 2]) ~> (senders = [r \in Process |-> 2])

\* With a broadcast, all correct processes eventually accept.
CorrLtl == (senders = [r \in Process |-> 1]) ~> (\A r \in correct : pc[r] = 2)

RelayLtl == (\E r \in correct : pc[r] = 2) ~> (\A r \in correct : pc[r] = 2)

====
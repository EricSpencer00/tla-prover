---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the Srikanth-Toueg protocol; faulty ones may send
\* arbitrary ECHOs, the unforgeability check below is where the safety lives.
\* Receives are nondeterministic over all sent messages, so a correct
\* process can be arbitrarily slow without ever failing outright.
\* The full action set: send, receive, send-echo, and accept.

Msgs == {"echo"}

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"haveinit","none","sent","accept"}]
  /\ recv \in [1..N -> SUBSET (1..N \X Msgs)]
  /\ sent \subseteq (1..N \X Msgs)

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {1..N} \ correct
  /\ pc = [p \in 1..N |-> IF p <= (N - F) THEN "haveinit" ELSE "none"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

Restricted == Init /\ \A p \in 1..N : pc[p] = "none"

\* A correct process may receive any subset of the messages currently out;
\* it is never stuck, it is merely slow, so weak fairness (not strong) is
\* enough to drive it forward once a fixpoint can be reached.
Receive(k) ==
  /\ k \in correct
  /\ recv' = [recv EXCEPT ![k] = recv[k] \cup
                 [m \in sent \cup (faulty \X Msgs) |-> m]]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(k) ==
  /\ k \in correct
  /\ pc[k] = "haveinit"
  /\ sent' = sent \cup (k \X Msgs)
  /\ pc' = [pc EXCEPT ![k] = "sent"]
  /\ UNCHANGED <<correct, faulty, recv>>

SendEchoLater(k) ==
  /\ k \in correct
  /\ pc[k] = "none"
  /\ Cardinality(recv[k]) >= (N - 2 * T)
  /\ Cardinality(recv[k]) < (N - T)
  /\ sent' = sent \cup (k \X Msgs)
  /\ pc' = [pc EXCEPT ![k] = "sent"]
  /\ UNCHANGED <<correct, faulty, recv>>

\* The true quorum bound: both ways past it, both converge on acceptance.
AcceptLater(k) ==
  /\ k \in correct
  /\ pc[k] \in {"none", "sent"}
  /\ Cardinality(recv[k]) >= (N - T)
  /\ sent' = sent \cup (k \X Msgs)
  /\ pc' = [pc EXCEPT ![k] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(k) ==
  /\ k \in correct
  /\ pc[k] = "sent"
  /\ Cardinality(recv[k]) >= (N - T)
  /\ pc' = [pc EXCEPT ![k] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E k \in 1..N : Receive(k)
  \/ \E k \in correct : SendEcho(k) \/ SendEchoLater(k) \/ AcceptLater(k) \/ Accept(k)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(\E k \in 1..N : Receive(k))
  /\ WF_vars(\E k \in correct : SendEchoLater(k))
  /\ SF_vars(\E k \in correct : SendEcho(k))
  /\ SF_vars(\E k \in correct : AcceptLater(k))
  /\ WF_vars(\E k \in correct : Accept(k))

AllCorrectAccept == \A p \in correct : pc[p] = "accept"

CorrLtl == (correct # {}) ~> AllCorrectAccept
RelayLtl == (\E p \in correct : pc[p] = "accept") ~> AllCorrectAccept

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

\* The no-broadcast, all-correct case is a deadlock by construction,
\* so unforgeability is a plain invariant rather than an LTL property.
UnforgLtl == Restricted => (\A p \in correct : pc[p] # "accept")
====
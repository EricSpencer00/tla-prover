---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* One-round asynchronous broadcast with Byzantine fault tolerance, based on
\* Srikanth and Toueg 1987 (Figure 7).  The INIT broadcast is encoded as an
\* initial value per process rather than a dedicated broadcaster.

CONSTANTS N, T, F

\* Control locations: whether a correct process has received the INIT message
\* (Rcv), not yet received it (Nxt), sent an ECHO message (Sent), or accepted.
Loc == { "Nxt", "Rcv", "Sent", "Acpt", "Term" }

VARIABLES correct, faulty, pc, recvd, sent

vars == << correct, faulty, pc, recvd, sent >>

TypeOK ==
  /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
  /\ Cardinality(correct) = N - F
  /\ pc \in [1..N -> Loc]
  /\ recvd \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sent \subseteq (1..N \X {"echo"})

\* The invariant protects the shape of the protocol; unforgeability below
\* protects the fact that no correct process accepts when no correct process
\* ever broadcast.
CorrLtl == (N - F) > (2 * T) /\ T >= F /\ F >= 0
UnforgLtl == (forall q \in correct : pc[q] = "Rcv") ~> (forall q \in correct : pc[q] = "Acpt")
RelayLtl == (\E q \in correct : pc[q] = "Acpt") ~> (\A q \in correct : pc[q] = "Acpt")

Init ==
  /\ correct = {1..(N - F)} /\ faulty = {1..N} \ correct
  /\ pc = [q \in 1..N |-> IF q \in correct THEN "Rcv" ELSE "Nxt"]
  /\ recvd = [q \in 1..N |-> {}]
  /\ sent = {}

InitNone ==
  /\ correct = {1..(N - F)} /\ faulty = {1..N} \ correct
  /\ pc = [q \in 1..N |-> "Nxt"]
  /\ recvd = [q \in 1..N |-> {}]
  /\ sent = {}

\* Correct processes only ever record messages sent by other correct processes;
\* the Byzantine ones are modelled as a nondeterministic set of possible
\* messages that any correct process may receive.
RecvStep(q) ==
  /\ q \in correct /\ pc[q] \in {"Rcv", "Nxt"}
  /\ recvd' = [recvd EXCEPT ![q] = recvd[q] \cup sent]
  /\ UNCHANGED << correct, faulty, pc, sent >>

RcvInitActs(q) ==
  /\ q \in correct /\ pc[q] = "Rcv"
  /\ sent' = sent \cup {<< q, "echo" >>}
  /\ pc' = [pc EXCEPT ![q] = "Acpt"]
  /\ UNCHANGED << correct, faulty, recvd >>

RcvEchoActs(q) ==
  /\ q \in correct /\ pc[q] \notin {"Acpt", "Term"}
  /\ Cardinality({s \in recvd[q] : s[2] = "echo"}) >= (N - 2 * T)
  /\ Cardinality({s \in recvd[q] : s[2] = "echo"}) < (N - T)
  /\ sent' = sent \cup {<< q, "echo" >>}
  /\ pc' = [pc EXCEPT ![q] = "Sent"]
  /\ UNCHANGED << correct, faulty, recvd >>

RcvEchoActsAcpt(q) ==
  /\ q \in correct /\ pc[q] \notin {"Acpt", "Term"}
  /\ Cardinality({s \in recvd[q] : s[2] = "echo"}) >= (N - T)
  /\ sent' = sent \cup {<< q, "echo" >>}
  /\ pc' = [pc EXCEPT ![q] = "Acpt"]
  /\ UNCHANGED << correct, faulty, recvd >>

RelayActs(q) ==
  /\ q \in correct /\ pc[q] = "Sent"
  /\ Cardinality({s \in recvd[q] : s[2] = "echo"}) >= (N - T)
  /\ pc' = [pc EXCEPT ![q] = "Acpt"]
  /\ UNCHANGED << correct, faulty, recvd, sent >>

Next ==
  \/ \E q \in 1..N : RecvStep(q)
  \/ \E q \in 1..N : RcvInitActs(q)
  \/ \E q \in 1..N : RcvEchoActs(q)
  \/ \E q \in 1..N : RcvEchoActsAcpt(q)
  \/ \E q \in 1..N : RelayActs(q)

Spec ==
  /\ Init /\ (\A q \in 1..N : SF_vars(RecvStep(q)))
  /\ (\A q \in 1..N : WF_vars(RcvInitActs(q)))
  /\ (\A q \in 1..N : WF_vars(RcvEchoActs(q)))
  /\ (\A q \in 1..N : WF_vars(RcvEchoActsAcpt(q)))
  /\ (\A q \in 1..N : WF_vars(RelayActs(q)))

FCConstraints == CorrLtl /\ UnforgLtl
====
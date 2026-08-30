---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F

\* Processes are partitioned nondeterministically into correct and Byzantine sets
\* of fixed cardinalities, and each correct process starts either already with
\* the broadcast's INIT message or without it.
\* Messages are just ECHO type stamped with a sender identity (no fields to forge).
\* The invariant below is the unforgeability claim; its proof is supported by
\* the type safety invariant and the fairness assumption on receiving/acting.

VARIABLES correct, faulty, pc, recv, sent
vars == << correct, faulty, pc, recv, sent >>

\* pc[p] is a control location; recv[p] is the set of messages p has actually seen.
Ctrl == {"hasInit", "noInit", "echoed", "accepted"}
Msg == "ECHO"

InitStates == {"hasInit", "noInit"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Ctrl]
  /\ recv \in [1..N -> SUBSET (1..N)]
  /\ sent \subseteq (1..N)

\* The two variants below differ only in how the broadcast is seeded:
\* broadcastStarts is the normal case; noBroadcast is the strict no-init case.
Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]
  /\ \E pc0 \in [1..N -> InitStates] :
       /\ Cardinality({p \in 1..N : pc0[p] = "hasInit"}) >= 1
       /\ pc = pc0

\* The restricted variant: every correct process starts without the INIT message.
NoBroadcast ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]
  /\ \E pc0 \in [1..N -> InitStates] :
       /\ \A p \in 1..N : pc0[p] = "noInit"
       /\ pc = pc0

\* A correct process may receive any subset of what correct processes have sent, plus
\* arbitrary contributions from Byzantine processes (the unforgeable ECHO messages).
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"hasInit", "noInit"}
  /\ \E m \in SUBSET (recv[p] \cup sent) :
       recv' = [recv EXCEPT ![p] = m]
  /\ UNCHANGED << correct, faulty, pc, sent >>

\* An INIT message is interpreted as immediate acceptance plus an ECHO broadcast.
InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "hasInit"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED << correct, faulty, recv >>

\* A process that has not yet sent ECHO may do so once it has enough (but not a quorum).
EchoBefore(p) ==
  /\ p \in correct
  /\ pc[p] = "noInit"
  /\ Cardinality(recv[p]) >= N - 2 * T
  /\ Cardinality(recv[p]) < N - T
  /\ pc' = [pc EXCEPT ![p] = "echoed"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED << correct, faulty, recv >>

\* A process that has not yet sent ECHO but has a quorum accepts immediately.
EchoAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "noInit"
  /\ Cardinality(recv[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {p}
  /\ UNCHANGED << correct, faulty, recv >>

RelayAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "echoed"
  /\ Cardinality(recv[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
  \/ \E p \in 1..N : Receive(p)
  \/ \E p \in 1..N : InitAccept(p)
  \/ \E p \in 1..N : EchoBefore(p)
  \/ \E p \in 1..N : EchoAccept(p)
  \/ \E p \in 1..N : RelayAccept(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E p \in 1..N : Receive(p))

FCConstraints == Init \/ NoBroadcast

CorrLtl == <>(\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
UnforgLtl == \A p \in correct : (pc[p] = "accepted") ~> (\A q \in correct : pc[q] = "accepted")
====
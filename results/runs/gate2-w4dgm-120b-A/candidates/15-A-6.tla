---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct participants are chosen nondeterministically at init; F <= T and
\* N > 3T are the fault and quorum bounds of the Srikanth-Toueg algorithm.
\* PC is the stage of the one-round broadcast; Msgs are (sender, kind).
\* Unforgeability is the safety property that fails when no correct broadcast
\* ever happens; CorrLtl/RelayLtl are its liveness complement.
\* Weak fairness (SF) on the combined receive-and-act steps is assumed only
\* for the liveness checking runs; the unforgeability check uses no fairness.

Nodes == 1..N

VARIABLES correct, faulty, pc, received, sent

vars == <<correct, faulty, pc, received, sent>>

TypeOK ==
  /\ correct \subseteq Nodes /\ Cardinality(correct) = N - F
  /\ faulty = Nodes \ correct
  /\ pc \in [Nodes -> {"idle", "nocast", "sent", "accepted"}]
  /\ received \in [Nodes -> SUBSET [n: Nodes, k: {"echo"}]]
  /\ sent \in SUBSET [n: Nodes, k: {"echo"}]

Init ==
  /\ \E s \in {x \in [Nodes -> {"idle", "nocast"}] : Cardinality({i \in Nodes : x[i] = "idle"}) = N - F} :
       /\ correct = {i \in Nodes : s[i] = "idle"}
       /\ pc = s
  /\ faulty = Nodes \ correct
  /\ received = [n \in Nodes |-> {}]
  /\ sent = {}

InitNoBroad ==
  /\ correct = {1..N} /\ faulty = {}
  /\ pc = [n \in Nodes |-> "nocast"]
  /\ received = [n \in Nodes |-> {}]
  /\ sent = {}

MsgFrom(f) == [n |-> f, k |-> "echo"]

\* Receive-union/sender-merge: a correct node may absorb any subset of the
\* already-sent correct messages together with any Byzantine sender guess.
Receive(n) ==
  /\ n \in correct /\ pc[n] \notin {"sent", "accepted"}
  /\ \E s \in SUBSET (sent \cup {MsgFrom(f) : f \in faulty}) : received' = [received EXCEPT ![n] = @ \cup s]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct node that started with the broadcast message accepts immediately
\* and sends its ECHO.
SendEcho(n) ==
  /\ n \in correct /\ pc[n] = "idle" /\ sent' = sent \cup {MsgFrom(n)}
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ UNCHANGED <<correct, faulty, received>>

EmitEcho(n) ==
  /\ n \in correct /\ pc[n] \notin {"sent", "accepted"}
  /\ Cardinality({m \in received[n] : m.k = "echo"}) >= N - 2 * T
  /\ Cardinality({m \in received[n] : m.k = "echo"}) < N - T
  /\ sent' = sent \cup {MsgFrom(n)}
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ UNCHANGED <<correct, faulty, received>>

AcceptFast(n) ==
  /\ n \in correct /\ pc[n] \notin {"sent", "accepted"}
  /\ Cardinality({m \in received[n] : m.k = "echo"}) >= N - T
  /\ sent' = sent \cup {MsgFrom(n)}
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<correct, faulty, received>>

AcceptSlow(n) ==
  /\ n \in correct /\ pc[n] = "sent"
  /\ Cardinality({m \in received[n] : m.k = "echo"}) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "accepted"]
  /\ UNCHANGED <<correct, faulty, received, sent>>

Next ==
  \/ \E n \in Nodes : Receive(n)
  \/ \E n \in Nodes : SendEcho(n)
  \/ \E n \in Nodes : EmitEcho(n)
  \/ \E n \in Nodes : AcceptFast(n)
  \/ \E n \in Nodes : AcceptSlow(n)

Spec == Init /\ [][Next]_vars
        /\ \A n \in Nodes : SF_vars(Receive(n)) /\ SF_vars(EmitEcho(n))
        /\ WF_vars(\E n \in Nodes : SendEcho(n)) /\ WF_vars(\E n \in Nodes : AcceptFast(n))
        /\ WF_vars(\E n \in Nodes : AcceptSlow(n))

CorrLtl == (\A n \in correct : pc[n] = "idle") ~> (\A n \in correct : pc[n] = "accepted")
RelayLtl == (\E n \in correct : pc[n] = "accepted") ~> (\A n \in correct : pc[n] = "accepted")
UnforgLtl == (\A n \in correct : pc[n] = "nocast") ~> (\A n \in correct : pc[n] = "nocast")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
====
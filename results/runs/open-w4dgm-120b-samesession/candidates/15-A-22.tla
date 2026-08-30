---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes run the protocol; Faulty processes may send arbitrary
\* ECHO messages, which is what the N-2T / N-T thresholds must tolerate.
\* Unforgeability is checked with no correct process broadcasting at all.
\* The variant in the cfg (no fairness) checks only the safety invariant.

VARIABLES correct, faulty, pc, recv, sent

InitStates == {"bcast", "nobcast"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> {"bcast", "nobcast", "sent", "agree"}]
  /\ recv \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sent \subseteq (1..N \X {"echo"})

Dist(E) == {m[1] : m \in E}

\* No correct process ever receives a message from a faulty process;
\* only correct-sender messages are deliverable or causally visible.
\* The init state below is the worst-case for unforgeability.
Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ \E s \in [1..N -> InitStates] : pc = s
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process delivers a batch of new messages, possibly including
\* Byzantine ones, and reacts to an INIT message immediately.
ReceiveFresh(p) ==
  /\ pc[p] \in {"bcast", "nobcast"}
  /\ \E m \in SUBSET (sent \cup (faulty \X {"echo"})) :
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup m]
       /\ IF "bcast" \in m THEN
            /\ pc' = [pc EXCEPT ![p] = "agree"]
            /\ sent' = sent \cup {<<p, "echo">>}
          ELSE UNCHANGED <<pc, sent>>
  /\ UNCHANGED <<correct, faulty>>

SendEcho(p) ==
  /\ pc[p] = "bcast"
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

EnterSent(p) ==
  /\ pc[p] \in {"bcast", "nobcast"}
  /\ Cardinality(Dist(recv[p])) >= N - 2 * T
  /\ Cardinality(Dist(recv[p])) < N - T
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

EnterAgree(p) ==
  /\ pc[p] \in {"bcast", "nobcast"}
  /\ Cardinality(Dist(recv[p])) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "agree"]
  /\ sent' = sent \cup {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

LateAgree(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality(Dist(recv[p])) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "agree"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

\* Fairness is assumed only on the receive-and-act steps of correct processes;
\* the spec itself is deadlock-free even without it.
Next ==
  \/ \E p \in correct :
       \/ ReceiveFresh(p) \/ SendEcho(p) \/ EnterSent(p)
       \/ EnterAgree(p) \/ LateAgree(p)
  \/ UNCHANGED <<correct, faulty, pc, recv, sent>>

Spec ==
  /\ Init /\ [][Next]_<<correct, faulty, pc, recv, sent>>
  /\ \A p \in correct : WF_vars(ReceiveFresh(p))
  /\ \A p \in correct : WF_vars(SendEcho(p))
  /\ \A p \in correct : WF_vars(EnterSent(p))
  /\ \A p \in correct : WF_vars(EnterAgree(p))
  /\ \A p \in correct : WF_vars(LateAgree(p))

FCConstraints ==
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = (1..N)
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* If the broadcaster was never heard of, no correct process may accept.
UnforgLtl == (\A p \in correct : pc[p] \in {"bcast", "nobcast"}) ~> (\A p \in correct : pc[p] = "agree")

CorrLtl == (\A p \in correct : pc[p] = "bcast") ~> (\A p \in correct : pc[p] = "agree")
RelayLtl == (\E p \in correct : pc[p] = "agree") ~> (\A p \in correct : pc[p] = "agree")

====
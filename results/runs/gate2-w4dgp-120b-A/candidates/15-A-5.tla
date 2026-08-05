---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N \in Nat /\ N >= 1 /\ T \in Nat /\ T >= 1 /\ F \in Nat /\ F >= 0

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Msgs == {"ECHO"}
BcastMsgs == {("ECHO", p) : p \in 1..N}

Range(f) == {f[i] : i \in DOMAIN f}

\* A correct process accepts once it hears enough ECHOs from DISTINCT senders:
\* N-2T is enough to send, N-T is enough to accept.
Followers(n, S) == {p \in S : Cardinality({m \in recv[n] : m[1] = "ECHO" /\ m[2] = p}) >= n}

InitState(bits) == [n \in 1..N |-> IF (bits[n] = 1) THEN "bcast" ELSE "nosend"]

Init ==
  /\ correct \subseteq (1..N) /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ Range(correct)
  /\ \E bits \in {0, 1}^N :
       pc = InitState(bits)
  /\ recv = [n \in 1..N |-> {}]
  /\ sent = {}

\* Correct processes receive a union of all correctly-sent messages plus any
\* messages Byzantine processes may conjure up.
ReceiveStep(n) ==
  /\ n \in correct
  /\ \E newMsgs \subseteq (sent \cup BcastMsgs) :
       recv' = [recv EXCEPT ![n] = recv[n] \cup newMsgs]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

BroadcastStep(n) ==
  /\ n \in correct
  /\ pc[n] = "bcast"
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ sent' = sent \cup {("ECHO", n)}
  /\ UNCHANGED <<correct, faulty, recv>>

RelayStep(n) ==
  /\ n \in correct
  /\ pc[n] = "nosend"
  /\ Cardinality(Followers(n, correct)) >= N - 2 * T
  /\ Cardinality(Followers(n, correct)) < N - T
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ sent' = sent \cup {("ECHO", n)}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptStep(n) ==
  /\ n \in correct
  /\ pc[n] \in {"nosend", "sent"}
  /\ Cardinality(Followers(n, correct)) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "sent"]
  /\ sent' = sent \cup {("ECHO", n)}
  /\ UNCHANGED <<correct, faulty, recv>>

RelayAcceptStep(n) ==
  /\ n \in correct
  /\ pc[n] = "sent"
  /\ Cardinality(Followers(n, correct)) >= N - T
  /\ UNCHANGED vars

Next ==
  \/ \E n \in 1..N : ReceiveStep(n)
  \/ \E n \in 1..N : BroadcastStep(n)
  \/ \E n \in 1..N : RelayStep(n)
  \/ \E n \in 1..N : AcceptStep(n)
  \/ \E n \in 1..N : RelayAcceptStep(n)

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty = (1..N) \ Range(correct)
  /\ pc \in [1..N -> {"nosend", "bcast", "sent"}]
  /\ recv \in [1..N -> SUBSET (Msgs \X (1..N))]
  /\ sent \subseteq BcastMsgs

\* Safety: if no correct process broadcast the INIT, none of them accepts.
FCConstraints ==
  ((\A n \in correct : pc[n] # "bcast") => (\A n \in correct : pc[n] # "sent"))
  /\ N > 3 * T /\ T >= F

CorrLtl == (\A n \in correct : pc[n] = "bcast") ~> (\A n \in correct : pc[n] = "sent")
RelayLtl == (\E n \in correct : pc[n] = "sent") ~> (\A n \in correct : pc[n] = "sent")
UnforgLtl == (\A n \in correct : pc[n] # "bcast") ~> (\A n \in correct : pc[n] # "sent")

\* Fairness on the combined receive-and-act steps of correct processes is what
\* carries this through to the end; the no-broadcast case can also be checked
\* without it (safety-only) against the same state space.
Spec ==
  /\ Init
  /\ (\A n \in 1..N : TRUE)
  /\ (\A n \in correct : WF_vars(ReceiveStep(n)))
  /\ (\A n \in correct : WF_vars(BroadcastStep(n)))
  /\ (\A n \in correct : WF_vars(RelayStep(n)))
  /\ (\A n \in correct : WF_vars(AcceptStep(n)))
  /\ (\A n \in correct : WF_vars(RelayAcceptStep(n)))

====
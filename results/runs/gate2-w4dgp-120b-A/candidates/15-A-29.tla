---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* One-round asynchronous reliable broadcast (Srikanth & Toueg, 1987) with
\* Byzantine faults. Each process is seeded with whether it received the
\* broadcaster's INIT message; correct processes follow the protocol, and
\* Byzantine ones may send arbitrary ECHO messages. Acceptance requires
\* a threshold of distinct ECHO messages, but a runaway Byzantine sender
\* can crash the quorum, so the safety invariant only rules out
\* acceptance when the broadcaster never sent anything, regardless of
\* how many Byzantine ECHOs arrive.

VARIABLES correct, faulty, loc, recvd, sent

vars == <<correct, faulty, loc, recvd, sent>>

None == "none"
Types == {"INIT", "NON"}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> {"boot", "noboot", "echo", "accept"}]
  /\ recvd \in [1..N -> SUBSET (1..N \X Types)]
  /\ sent \subseteq (1..N \X Types)

Init ==
  /\ correct = CHOOSE c \in (SUBSET (1..N)) : Cardinality(c) = N - F
  /\ faulty = (1..N) \ correct
  /\ \E s \in (SUBSET (1..N)):
       /\ Cardinality(s) = N - F
       /\ loc = [i \in 1..N |-> IF i \in s THEN "boot" ELSE "noboot"]
  /\ recvd = [i \in 1..N |-> {}]
  /\ sent = {}

\* A correct process absorbs any messages it has not yet seen from correct
\* senders or from a Byzantine sender (the power set here forces a full
\* interleaving for fairness to make progress on arbitrary deliveries).
Receive(i) ==
  /\ i \in correct
  /\ loc[i] # "accept"
  /\ recvd' = [recvd EXCEPT ![i] =
        recvd[i] \cup ({p \in correct : <<p, "INIT">> \in sent} \cup {p \in faulty : <<p, "INIT">> \in sent})]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

\* Receiving the broadcaster's INIT message immediately accepts and
\* broadcasts an ECHO to all.
Broadcast(i) ==
  /\ i \in correct
  /\ loc[i] = "boot"
  /\ loc' = [loc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<i, "INIT">>}
  /\ UNCHANGED <<correct, faulty, recvd>>

\* Below quorum, but at least enough to form a valid group of honest senders.
RelayLow(i) ==
  /\ i \in correct
  /\ loc[i] \in {"noboot", "boot"}
  /\ Cardinality({j \in recvd[i] : j[2] = "INIT"}) >= N - 2 * T
  /\ Cardinality({j \in recvd[i] : j[2] = "INIT"}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "echo"]
  /\ sent' = sent \cup {<<i, "INIT">>}
  /\ UNCHANGED <<correct, faulty, recvd>>

RelayThresh(i) ==
  /\ i \in correct
  /\ loc[i] \in {"noboot", "boot"}
  /\ Cardinality({j \in recvd[i] : j[2] = "INIT"}) >= N - T
  /\ loc' = [loc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<i, "INIT">>}
  /\ UNCHANGED <<correct, faulty, recvd>>

RelayAccept(i) ==
  /\ i \in correct
  /\ loc[i] = "echo"
  /\ Cardinality({j \in recvd[i] : j[2] = "INIT"}) >= N - T
  /\ loc' = [loc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, recvd, sent>>

Next ==
  \/ \E i \in 1..N: Receive(i)
  \/ \E i \in 1..N: Broadcast(i)
  \/ \E i \in 1..N: RelayLow(i)
  \/ \E i \in 1..N: RelayThresh(i)
  \/ \E i \in 1..N: RelayAccept(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N: Receive(i))
  /\ WF_vars(\E i \in 1..N: Broadcast(i))
  /\ WF_vars(\E i \in 1..N: RelayLow(i))
  /\ WF_vars(\E i \in 1..N: RelayThresh(i))
  /\ WF_vars(\E i \in 1..N: RelayAccept(i))

\* A version of Spec with no fairness, for checking safety-only
SpecNoFair == Init /\ [][Next]_vars

\* No broadcast: if the broadcaster never seeded any correct process,
\* no correct process ever reaches accept (unforgeability).
UnforgLtl == (\A i \in correct: loc[i] = "noboot") ~> (\A i \in correct: loc[i] = "accept")

CorrLtl == (\A i \in correct: loc[i] = "boot") ~> (\A i \in correct: loc[i] = "accept")
RelayLtl == (\E k \in correct: loc[k] = "accept") ~> (\A i \in correct: loc[i] = "accept")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====
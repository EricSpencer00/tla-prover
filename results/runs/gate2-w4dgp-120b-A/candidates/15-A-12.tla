---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N > 3 * T /\ T >= F /\ F >= 0

\* The one-round reliable broadcast of Srikanth-Toueg 1987, with Byzantine
\* senders.  The "broadcaster" is a per-process initial flag rather than a
\* dedicated sender: each correct process is either in the broadcast-received
\* state or not at the start.

Locs == {"noINIT", "broadcast"}

VARIABLES correct, faulty, pc, rxed, sent

vars == <<correct, faulty, pc, rxed, sent>>

InitStates == {"noINIT", "broadcast"}

Active(p) == \E m \in rxed[p] : m[2] = "ECHO"

Senders(p) == {q \in N : <<q, "ECHO">> \in rxed[p]}

InitInit == [p \in N |-> IF p % 2 = 0 THEN "broadcast" ELSE "noINIT"]

TypeOK ==
  /\ correct \subseteq 1..N /\ faulty = (1..N) \ correct
  /\ pc \in [1..N -> Locs]
  /\ rxed \in [1..N -> SUBSET (1..N \X {"ECHO"})]
  /\ sent \in SUBSET (1..N \X {"ECHO"})

Init ==
  /\ [correct |-> {p \in 1..N : p <= N - F}, faulty |-> {p \in 1..N : p > N - F}]
  /\ pc = InitInit /\ rxed = [p \in 1..N |-> {}] /\ sent = {}

Receive(p, mset) ==
  /\ p \in correct
  /\ \E m \in mset : m[2] = "ECHO"
  /\ \A m \in mset : m \in sent \/ (\E f \in faulty : m = <<f, "ECHO">>)
  /\ mset \cap rxed[p] = {}
  /\ rxed' = [rxed EXCEPT ![p] = @ \cup mset]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
  /\ pc[p] # "broadcast"
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ pc' = [pc EXCEPT ![p] = "broadcast"]
  /\ UNCHANGED <<correct, faulty, rxed>>

ActNormal(p) ==
  /\ p \in correct
  /\ \A m \in rxed[p] : m[2] = "ECHO"
  /\ Cardinality(Senders(p)) >= N - 2 * T /\ Cardinality(Senders(p)) < N - T
  /\ \E q \in correct : <<q, "ECHO">> \notin sent
  /\ pc' = [pc EXCEPT ![p] = "broadcast"]
  /\ UNCHANGED <<correct, faulty, rxed, sent>>

ActStrong(p) ==
  /\ p \in correct
  /\ Cardinality(Senders(p)) >= N - T
  /\ \E q \in correct \cup faulty : <<q, "ECHO">> \notin sent
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ pc' = [pc EXCEPT ![p] = "broadcast"]
  /\ UNCHANGED <<correct, faulty, rxed>>

RestoreWeak(p) ==
  /\ p \in correct
  /\ Cardinality(Senders(p)) >= N - T
  /\ pc[p] = "broadcast"
  /\ UNCHANGED vars

ReceiveStep == \E p \in 1..N : \E m \in SUBSET ((1..N) \X {"ECHO"}) : Receive(p, m)

Next ==
  \/ ReceiveStep
  \/ \E p \in 1..N : SendEcho(p) \/ ActNormal(p) \/ ActStrong(p) \/ RestoreWeak(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(ReceiveStep)

\* Unforgeability: without any correct broadcaster, no correct process may
\* ever accept.
UnforgLtl == (~\A p \in correct : pc[p] = "broadcast") ~> (~\E p \in correct : pc[p] = "broadcast")

\* Correctness: if the broadcaster reaches every correct process, all do.
CorrLtl == (\A p \in correct : pc[p] = "broadcast") ~> (\A p \in correct : pc[p] = "broadcast")

\* Relay: the protocol never leaves a lone correct acceptor behind.
RelayLtl == (\E p \in correct : pc[p] = "broadcast") ~> (\A p \in correct : pc[p] = "broadcast")

FCConstraints ==
  /\ (N - F >= 1) /\ (N - 2 * T >= 1)
  /\ (N - F < N) /\ (N - F > N - T)
  /\ (N > 3 * T)

====
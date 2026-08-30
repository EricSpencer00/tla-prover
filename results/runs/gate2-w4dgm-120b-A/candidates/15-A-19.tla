---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F
\* N processes, at most T Byzantine. Correct processes broadcast INIT or not
\* as an initial value rather than a dedicated broadcaster.

\* Control locations: broadcast received (init), not received (none), ECHO sent
\* but not yet accepted (echoed), and accepted. Message is a pair (sender, type).
Locations == {"init", "none", "echoed", "accepted"}
MsgTypes == {"echo"}
Pairs == {p \in 1..N : <<p, "echo">>}

VARIABLES correct, faulty, pc, rcvd, sent

vars == <<correct, faulty, pc, rcvd, sent>>

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ pc \in [1..N -> Locations]
  /\ rcvd \in [1..N -> SUBSET Pairs]
  /\ sent \subseteq Pairs

Init ==
  \E S \in SUBSET 1..N :
    /\ Cardinality(S) = N - F
    /\ correct = S
    /\ faulty = 1..N \ S
    /\ pc \in [p \in 1..N |-> IF p \in S THEN "init" ELSE "none"]
    /\ rcvd = [p \in 1..N |-> {}]
    /\ sent = {}

\* A correct process may receive any subset of all sent messages, plus any
\* Byzantine messages (the latter are never counted toward the quorum).
Receive ==
  \E p \in correct, m \in SUBSET Pairs :
    /\ pc[p] \in {"init", "none"}
    /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup m]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A correct process that got the broadcast accepts immediately and sends ECHO.
BroadcastAccept ==
  \E p \in correct :
    /\ pc[p] = "init"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ UNCHANGED <<correct, faulty, rcvd>>

\* A correct process that has not yet sent ECHO receives >= N-2T ECHOs and sends.
EchoSend ==
  \E p \in correct :
    /\ pc[p] = "none"
    /\ Cardinality(rcvd[p] \cap Pairs) >= N - 2 * T
    /\ Cardinality(rcvd[p] \cap Pairs) < N - T
    /\ pc' = [pc EXCEPT ![p] = "echoed"]
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ UNCHANGED <<correct, faulty, rcvd>>

\* A correct process that has not yet sent ECHO receives >= N-T ECHOs and accepts.
EchoAccept ==
  \E p \in correct :
    /\ pc[p] = "none"
    /\ Cardinality(rcvd[p] \cap Pairs) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ UNCHANGED <<correct, faulty, rcvd>>

\* A correct process that sent ECHO accepts once it has collected >= N-T ECHOs.
LateAccept ==
  \E p \in correct :
    /\ pc[p] = "echoed"
    /\ Cardinality(rcvd[p] \cap Pairs) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, rcvd, sent>>

Next == Receive \/ BroadcastAccept \/ EchoSend \/ EchoAccept \/ LateAccept

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Receive) /\ WF_vars(BroadcastAccept) /\ WF_vars(EchoSend)
  /\ WF_vars(EchoAccept) /\ WF_vars(LateAccept)

\* If no correct process broadcasts, no correct process ever accepts.
UnforgLtl == (\A p \in correct: pc[p] # "init") ~> (\A p \in correct: pc[p] = "accepted")
CorrLtl == (\A p \in correct: pc[p] = "init") ~> (\A p \in correct: pc[p] = "accepted")
RelayLtl == (\E p \in correct: pc[p] = "accepted") ~> (\A p \in correct: pc[p] = "accepted")
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A process is a correct participant only if it is in the correct set; a
\* faulty one is never assumed to behave.
\* Two initial states exist: with INIT received by correct processes, and
\* with INIT received by nobody (the no-broadcast case).
\* The two delivery actions are combined so that a correctness action is
\* only weakly fair on the combined receive-and-act step, not on each
\* individually -- that is what the fairness comment at the end means.

VARIABLES correct, faulty, loc, recv, sent

Locs == {"init","noinit","sent","accept"}
Msgs == {"echo"}
Vars == <<correct, faulty, loc, recv, sent>>

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> Locs]
  /\ recv \in [1..N -> SUBSET (1..N \X Msgs)]
  /\ sent \subseteq (1..N \X Msgs)

\* Unforgeability: with nobody broadcasting, no correct process accepts.
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ faulty = (1..N) \ correct
  /\ UNCHANGED <<correct, faulty>>

EchoFrom(y, m) == m = "echo" /\ y \in correct

Init ==
  /\ correct = {}
  /\ faulty = {}
  /\ loc = [p \in 1..N |-> "init"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

\* The restricted start: no correct process received the INIT message.
InitNoBroad ==
  /\ correct = {}
  /\ faulty = {}
  /\ loc = [p \in 1..N |-> "noinit"]
  /\ recv = [p \in 1..N |-> {}]
  /\ sent = {}

RecvMsgs(p) ==
  /\ loc[p] \in {"init","noinit"}
  /\ \E g \in SUBSET ((correct \union faulty) \X Msgs):
       recv' = [recv EXCEPT ![p] = recv[p] \union g]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

SendEchoAccept(p) ==
  /\ p \in correct
  /\ loc[p] = "init"
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ sent' = sent \union {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

SendEchoDeliberate(p) ==
  /\ p \in correct
  /\ loc[p] = "noinit"
  /\ Cardinality({y \in 1..N : EchoFrom(y, recv[p])}) >= N - 2 * T
  /\ Cardinality({y \in 1..N : EchoFrom(y, recv[p])}) < N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \union {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

SendEchoAcceptThreshold(p) ==
  /\ p \in correct
  /\ loc[p] = "noinit"
  /\ Cardinality({y \in 1..N : EchoFrom(y, recv[p])}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ sent' = sent \union {<<p, "echo">>}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptAfterSent(p) ==
  /\ p \in correct
  /\ loc[p] = "sent"
  /\ Cardinality({y \in 1..N : EchoFrom(y, recv[p])}) >= N - T
  /\ loc' = [loc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ RecvMsgs(1) \/ RecvMsgs(2) \/ RecvMsgs(3) \/ RecvMsgs(4)
  \/ SendEchoAccept(1) \/ SendEchoAccept(2) \/ SendEchoAccept(3) \/ SendEchoAccept(4)
  \/ SendEchoDeliberate(1) \/ SendEchoDeliberate(2) \/ SendEchoDeliberate(3) \/ SendEchoDeliberate(4)
  \/ SendEchoAcceptThreshold(1) \/ SendEchoAcceptThreshold(2)
       \/ SendEchoAcceptThreshold(3) \/ SendEchoAcceptThreshold(4)
  \/ AcceptAfterSent(1) \/ AcceptAfterSent(2) \/ AcceptAfterSent(3) \/ AcceptAfterSent(4)

Spec ==
  /\ Init \/ InitNoBroad
  /\ [][Next]_Vars
  /\ WF_Vars(RecvMsgs(1)) /\ WF_Vars(SendEchoAccept(1)) /\ WF_Vars(SendEchoDeliberate(1))
       /\ WF_Vars(SendEchoAcceptThreshold(1)) /\ WF_Vars(AcceptAfterSent(1))
  /\ WF_Vars(RecvMsgs(2)) /\ WF_Vars(SendEchoAccept(2)) /\ WF_Vars(SendEchoDeliberate(2))
       /\ WF_Vars(SendEchoAcceptThreshold(2)) /\ WF_Vars(AcceptAfterSent(2))
  /\ WF_Vars(RecvMsgs(3)) /\ WF_Vars(SendEchoAccept(3)) /\ WF_Vars(SendEchoDeliberate(3))
       /\ WF_Vars(SendEchoAcceptThreshold(3)) /\ WF_Vars(AcceptAfterSent(3))
  /\ WF_Vars(RecvMsgs(4)) /\ WF_Vars(SendEchoAccept(4)) /\ WF_Vars(SendEchoDeliberate(4))
       /\ WF_Vars(SendEchoAcceptThreshold(4)) /\ WF_Vars(AcceptAfterSent(4))

CorrLtl == \A p \in 1..N : (p \in correct /\ loc[p] = "init") ~> (loc[p] = "accept")
RelayLtl == \E p \in 1..N : loc[p] = "accept" ~> (\A q \in 1..N : loc[q] = "accept")
UnforgLtl == (\A p \in 1..N : p \in correct => loc[p] # "init") ~> (\A p \in 1..N : loc[p] = "accept")

====
---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Identifiers: N is number of processes, T is the Byzantine bound, and F is
\* the number of processes that are actually faulty (chosen nondeterministically,
\* but always at most the bound T). CorrLtl and RelayLtl are LIVENESS
\* properties; UnforgLtl is the safety property proving no acceptance without a
\* broadcast. FCConstraints is the type invariant.

Processes == 0 .. (N - 1)
MsgTypes == {"ECHO"}
InitStates == {"nob", "brd"}
Stages == {"init", "echoed", "done", "none"}

VARIABLES correct, faulty, loc, recv, sent
vars == << correct, faulty, loc, recv, sent >>

TypeOK ==
    /\ correct \subseteq Processes
    /\ faulty \subseteq Processes
    /\ correct \cap faulty = {}
    /\ loc \in [Processes -> Stages]
    /\ recv \in [Processes -> SUBSET (Processes \X MsgTypes)]
    /\ sent \subseteq (Processes \X MsgTypes)

Init ==
    /\ Cardinality(correct) = N - F
    /\ faulty = Processes \ correct
    /\ sent = {}
    /\ loc = [p \in Processes |-> "init"]
    /\ recv = [p \in Processes |-> {}]

NoBroadcast ==
    /\ Cardinality(correct) = N - F
    /\ faulty = Processes \ correct
    /\ sent = {}
    /\ loc = [p \in Processes |-> IF p \in correct THEN "brd" ELSE "nob"]
    /\ recv = [p \in Processes |-> {}]

\* A correct process receives any subset of messages: those sent by correct
\* processes plus any (adversarial) message from a faulty process.
Receive(p) ==
    /\ loc[p] = "init"
    /\ \E m \in SUBSET (sent \cup (faulty \X MsgTypes)):
         recv' = [recv EXCEPT ![p] = recv[p] \cup m]
    /\ UNCHANGED << correct, faulty, loc, sent >>

\* A correct process that received the broadcaster's INIT message accepts and
\* sends an ECHO vote to all other processes.
BroadcastEcho(p) ==
    /\ p \in correct
    /\ loc[p] = "init"
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ sent' = sent \cup ({p} \X MsgTypes)
    /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent an echo gathers a quorum of N-2T
\* votes from distinct senders and sends its echo without accepting yet.
GatherEcho(p) ==
    /\ p \in correct
    /\ loc[p] = "init"
    /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N - 2 * T
    /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) < N - T
    /\ loc' = [loc EXCEPT ![p] = "echoed"]
    /\ sent' = sent \cup ({p} \X MsgTypes)
    /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that has not yet sent an echo gathers a quorum of N-T
\* votes and accepts in the same step.
AcceptEcho(p) ==
    /\ p \in correct
    /\ loc[p] = "init"
    /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ sent' = sent \cup ({p} \X MsgTypes)
    /\ UNCHANGED << correct, faulty, recv >>

\* A correct process that already echoed accepts once it has gathered a quorum
\* of N-T votes.
AcceptEchoLater(p) ==
    /\ p \in correct
    /\ loc[p] = "echoed"
    /\ Cardinality({q \in Processes : <<q, "ECHO">> \in recv[p]}) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
    \/ Receive(0) \/ Receive(1) \/ Receive(2) \/ Receive(3)
    \/ BroadcastEcho(0) \/ BroadcastEcho(1) \/ BroadcastEcho(2) \/ BroadcastEcho(3)
    \/ GatherEcho(0) \/ GatherEcho(1) \/ GatherEcho(2) \/ GatherEcho(3)
    \/ AcceptEcho(0) \/ AcceptEcho(1) \/ AcceptEcho(2) \/ AcceptEcho(3)
    \/ AcceptEchoLater(0) \/ AcceptEchoLater(1) \/ AcceptEchoLater(2) \/ AcceptEchoLater(3)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Receive(0)) /\ WF_vars(Receive(1)) /\ WF_vars(Receive(2)) /\ WF_vars(Receive(3))
        /\ WF_vars(BroadcastEcho(0)) /\ WF_vars(BroadcastEcho(1)) /\ WF_vars(BroadcastEcho(2)) /\ WF_vars(BroadcastEcho(3))
        /\ WF_vars(GatherEcho(0)) /\ WF_vars(GatherEcho(1)) /\ WF_vars(GatherEcho(2)) /\ WF_vars(GatherEcho(3))
        /\ WF_vars(AcceptEcho(0)) /\ WF_vars(AcceptEcho(1)) /\ WF_vars(AcceptEcho(2)) /\ WF_vars(AcceptEcho(3))
        /\ WF_vars(AcceptEchoLater(0)) /\ WF_vars(AcceptEchoLater(1)) /\ WF_vars(AcceptEchoLater(2)) /\ WF_vars(AcceptEchoLater(3))

\* No acceptance can ever register unless some correct process has actually
\* broadcast: this is the safety (not liveness) property, which holds with
\* or without fairness (Fischer-Lynch-Patterson's impossibility theorem forces
\* a truthful-no-broadcast outcome regardless of the scheduler).
UnforgLtl == (\A p \in correct : loc[p] = "done") => (\E p \in correct : loc[p] = "init")
CorrLtl == (\A p \in correct : loc[p] = "init") ~> (\A p \in correct : loc[p] = "done")
RelayLtl == (\E p \in correct : loc[p] = "done") ~> (\A p \in correct : loc[p] = "done")

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
====
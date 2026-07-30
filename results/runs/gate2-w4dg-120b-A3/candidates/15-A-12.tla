---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* Model of a one-round asynchronous reliable broadcast with Byzantine faults.
\* Each process's initial state (StartInit or StartNoInit) stands in for whether
\* the broadcaster's INIT message was already received.
\* Actions: RecvAll (receive a set of messages), SendEcho, SendEchoQuorum,
\* SendEchoDecide, Decide.

CONSTANTS N, T, F

Ham\{s, t\} == Cardinality(s \cup t) - Cardinality(s \cap t)

Processes == 0..(N - 1)
NONE == 99
MsgKinds == {"ECHO"}
Msgs == [snd: Processes, kind: MsgKinds]
MsgsFrom(S) == {m \in Msgs : m.snd \in S}

VARIABLES correct, faulty, pc, rx, sent

vars == <<correct, faulty, pc, rx, sent>>

StartInit == [p \in Processes |-> IF p = 0 THEN "hasInit" ELSE "noInit"]
StartNoInit == [p \in Processes |-> "noInit"]

TypeOK ==
    /\ correct \subseteq Processes /\ faulty \subseteq Processes
    /\ pc \in [Processes -> {"noInit", "hasInit", "sent", "decided"}]
    /\ rx \in [Processes -> SUBSET Msgs]
    /\ sent \subseteq Msgs

FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ Cardinality(faulty) = F
    /\ N > 3 * T /\ T >= F /\ F >= 0
    /\ correct \cap faulty = {} /\ correct \cup faulty = Processes
    /\ \A p \in Processes : pc[p] = "hasInit" => p \in correct

Init ==
    /\ correct = {p \in Processes : p < (N - F)}
    /\ faulty = Processes \ correct
    /\ pc = StartInit
    /\ rx = [p \in Processes |-> {}]
    /\ sent = {}

InitNoBroad ==
    /\ correct = {p \in Processes : p < (N - F)}
    /\ faulty = Processes \ correct
    /\ pc = StartNoInit
    /\ rx = [p \in Processes |-> {}]
    /\ sent = {}

\* A correct process receives a set of new messages, drawn from all correct
\* senders plus every possible Byzantine sender/message.
RecvAll(p, d) ==
    /\ p \in correct
    /\ pc[p] \in {"noInit", "hasInit"}
    /\ d # {}
    /\ d \subseteq (MsgsFrom(correct) \cup Msgs)
    /\ d \cap rx[p] = {}
    /\ rx' = [rx EXCEPT ![p] = rx[p] \cup d]
    /\ pc' = [pc EXCEPT ![p] = IF pc[p] = "hasInit" THEN "sent" ELSE "noInit"]
    /\ UNCHANGED <<correct, faulty, sent>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "hasInit"
    /\ sent' = sent \cup {[snd |-> p, kind |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, rx>>

SendEchoQuorum(p) ==
    /\ p \in correct
    /\ pc[p] = "noInit"
    /\ Ham(rx[p], MsgsFrom(correct)) >= N - 2 * T
    /\ Ham(rx[p], MsgsFrom(correct)) < N - T
    /\ sent' = sent \cup {[snd |-> p, kind |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, rx>>

SendEchoDecide(p) ==
    /\ p \in correct
    /\ pc[p] = "noInit"
    /\ Ham(rx[p], MsgsFrom(correct)) >= N - T
    /\ sent' = sent \cup {[snd |-> p, kind |-> "ECHO"]}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, rx>>

Decide(p) ==
    /\ p \in correct
    /\ pc[p] = "sent"
    /\ Ham(rx[p], MsgsFrom(correct)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<correct, faulty, rx, sent>>

Next ==
    \/ \E p \in Processes, d \in SUBSET Msgs : RecvAll(p, d)
    \/ \E p \in Processes : SendEcho(p) \/ SendEchoQuorum(p)
                           \/ SendEchoDecide(p) \/ Decide(p)

W4Recvd == \A p \in correct : (pc[p] = "noInit") ~> (pc[p] \in {"sent", "decided"})
Spec == Init /\ [][Next]_vars /\ WF_vars(W4Recvd)

CorrLtl ==
    /\ (\A p \in correct : pc[p] = "hasInit") ~> (\A q \in correct : pc[q] = "decided")
    /\ (\A p \in correct : pc[p] = "sent") ~> (\A q \in correct : pc[q] = "decided")

RelayLtl == (\E p \in correct : pc[p] = "decided") ~> (\A q \in correct : pc[q] = "decided")

\* No process ever accepts unless some correct process actually broadcasted.
UnforgLtl == (\A p \in correct : pc[p] \in {"noInit", "hasInit"}) ~> (\A q \in correct : pc[q] = "noInit")

====
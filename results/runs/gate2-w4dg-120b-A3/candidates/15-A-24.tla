---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Nodes == 1..N
MsgTypes == {"ECHO"}
Msgs == [fr: Nodes, tp: MsgTypes]

VARIABLES correct, faulty, pc, recvd, sent

vars == <<correct, faulty, pc, recvd, sent>>

TypeOK ==
    /\ correct \subseteq Nodes
    /\ faulty \subseteq Nodes
    /\ pc \in [Nodes -> {"initRecvd", "initNone", "sentEcho", "accepted"}]
    /\ recvd \in [Nodes -> SUBSET Msgs]
    /\ sent \subseteq Msgs

FCConstraints ==
    /\ Cardinality(correct) = N - F
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = Nodes
    /\ Cardinality(Nodes) > 3 * T
    /\ T >= F
    /\ F >= 0

Age(p) == Cardinality({m \in recvd[p] : m.tp = "ECHO"})

Init ==
    /\ correct \subseteq Nodes
    /\ faulty = Nodes \ correct
    /\ Cardinality(correct) = N - F
    /\ pc \in [Nodes -> {"initRecvd", "initNone", "sentEcho", "accepted"}]
    /\ recvd \in [Nodes -> {}]
    /\ sent = {}

\* A restricted start where no correct process received the broadcast INIT.
InitNone ==
    /\ Init
    /\ \A p \in correct : pc[p] = "initNone"

\* A correct process always receives messages from correct senders, plus any
\* arbitrary set of messages from the Byzantine faulty processes.
ReceiveNew(p, ms) ==
    /\ p \in correct
    /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup (ms \cap {m \in sent : m.fr \in correct})]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

StartFromInit(p) ==
    /\ p \in correct
    /\ pc[p] = "initRecvd"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup {[fr |-> p, tp |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, recvd>>

EchoWithoutAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"initNone", "initRecvd"}
    /\ Age(p) >= N - 2 * T
    /\ Age(p) < N - T
    /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
    /\ sent' = sent \cup {[fr |-> p, tp |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, recvd>>

EchoThenAccept(p) ==
    /\ p \in correct
    /\ pc[p] \in {"initNone", "initRecvd"}
    /\ Age(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = sent \cup {[fr |-> p, tp |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, recvd>>

Accept(p) ==
    /\ p \in correct
    /\ pc[p] = "sentEcho"
    /\ Age(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recvd, sent>>

ReceiveStep(p, ms) == ReceiveNew(p, ms) \/ StartFromInit(p) \/ EchoWithoutAccept(p) \/ EchoThenAccept(p)

CorrectStep ==
    \E p \in correct : \E ms \in SUBSET Msgs : ReceiveStep(p, ms)

Next ==
    \/ \E p \in correct, ms \in SUBSET Msgs : ReceiveStep(p, ms)
    \/ \E p \in correct : Accept(p)

\* Weak fairness on the combined receive-and-act step for each correct process;
\* and a separate strong fairness on the final acceptance step, needed only if
\* a process stalls as initRecvd before ever growing recvd.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(CorrectStep)
    /\ SF_vars(\E p \in correct : Accept(p))

CorrLtl == <>(\A p \in correct : pc[p] = "accepted")
RelayLtl == (<> (\E p \in correct : pc[p] = "accepted")) ~> (\A p \in correct : pc[p] = "accepted")

\* Unforgeability: without a broadcast, no correct process ever accepts.
UnforgLtl == (\A p \in correct : pc[p] = "initNone") ~> (\A p \in correct : pc[p] # "accepted")

====
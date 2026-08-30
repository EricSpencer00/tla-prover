---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

NoneS == "nosender"
Types == {"init", "nobroadcast"}

VARIABLES correct, faulty, pc, inbox, sentMsgs

Vars == <<correct, faulty, pc, inbox, sentMsgs>>

MessageSpace == (1..N) \X {"ECHO"} \cup {<<NoneS, "INIT">>}

\* pc: control location (broadcast-received vs not); inbox: messages each process has received.
\* sentMsgs: messages actually emitted by correct processes (bounded by N).
InitRecords == CHOOSE p \in 1..N : TRUE

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ SumOver([p \in 1..N |-> IF p \in correct THEN 1 ELSE 0], 1..N) = N - F
    /\ SumOver([p \in 1..N |-> IF p \in faulty THEN 1 ELSE 0], 1..N) = F
    /\ pc \in [1..N -> Types]
    /\ inbox \in [1..N -> SUBSET MessageSpace]
    /\ sentMsgs \subseteq (1..N) \X {"ECHO"}

Init ==
    /\ correct = {p \in 1..N : p <= N - F}
    /\ faulty = {p \in 1..N : p > N - F}
    /\ sentMsgs = {}
    /\ pc = [p \in 1..N |-> IF p = InitRecords THEN "init" ELSE "nobroadcast"]
    /\ inbox = [p \in 1..N |-> {}]

InitRestricted ==
    /\ correct = {p \in 1..N : p <= N - F}
    /\ faulty = {p \in 1..N : p > N - F}
    /\ sentMsgs = {}
    /\ pc = [p \in 1..N |-> "nobroadcast"]
    /\ inbox = [p \in 1..N |-> {}]

\* A correct process may receive an arbitrary set of new messages, including Byzantine ones.
ReceiveMsgs(p) ==
    /\ p \in correct
    /\ \E R \in SUBSET (sentMsgs \cup (faulty \X {"ECHO"})):
         inbox' = [inbox EXCEPT ![p] = @ \cup R]
    /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

SendEcho(p) ==
    /\ p \in correct
    /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = "init"]
    /\ UNCHANGED <<correct, faulty, inbox>>

\* N-2T witnesses are enough to send ECHO without yet accepting.
SendEchoMid(p) ==
    /\ p \in correct
    /\ pc[p] = "nobroadcast"
    /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) >= N - 2 * T
    /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) < N - T
    /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, pc, inbox>>

ReceiveAndAccept(p) ==
    /\ p \in correct
    /\ pc[p] # "init"
    /\ Cardinality({q \in 1..N : <<q, "ECHO">> \in inbox[p]}) >= N - T
    /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
    /\ pc' = [pc EXCEPT ![p] = "init"]
    /\ UNCHANGED <<correct, faulty, inbox>>

AcceptOnly(p) ==
    /\ p \in correct
    /\ pc[p] = "init"
    /\ <<p, "ECHO">> \notin sentMsgs
    /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, pc, inbox>>

Next ==
    \/ ReceiveMsgs(InitRecords) \/ ReceiveMsgs(InitRecords + 1) \/ ReceiveMsgs(InitRecords + 2) \/ ReceiveMsgs(InitRecords + 3)
    \/ SendEcho(InitRecords) \/ SendEcho(InitRecords + 1) \/ SendEcho(InitRecords + 2) \/ SendEcho(InitRecords + 3)
    \/ SendEchoMid(InitRecords) \/ SendEchoMid(InitRecords + 1) \/ SendEchoMid(InitRecords + 2) \/ SendEchoMid(InitRecords + 3)
    \/ ReceiveAndAccept(InitRecords) \/ ReceiveAndAccept(InitRecords + 1) \/ ReceiveAndAccept(InitRecords + 2) \/ ReceiveAndAccept(InitRecords + 3)
    \/ AcceptOnly(InitRecords) \/ AcceptOnly(InitRecords + 1) \/ AcceptOnly(InitRecords + 2) \/ AcceptOnly(InitRecords + 3)

\* Under weak fairness on receive-and-act steps, the broadcast always completes among correct participants.
Spec == Init /\ [][Next]_Vars
    /\ WF_Vars(ReceiveMsgs(InitRecords) \/ ReceiveAndAccept(InitRecords))
    /\ WF_Vars(ReceiveMsgs(InitRecords + 1) \/ ReceiveAndAccept(InitRecords + 1))
    /\ WF_Vars(ReceiveMsgs(InitRecords + 2) \/ ReceiveAndAccept(InitRecords + 2))
    /\ WF_Vars(ReceiveMsgs(InitRecords + 3) \/ ReceiveAndAccept(InitRecords + 3))

\* No correct broadcast at all (no INIT anywhere) must never lead to a correct acceptance.
UnforgLtl == (\A p \in 1..N : pc[p] = "nobroadcast") ~> (\A p \in correct : pc[p] = "init")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "init")
RelayLtl == (\E p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "init")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====
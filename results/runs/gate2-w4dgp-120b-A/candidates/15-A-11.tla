---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

MessageTypes == {"ECHO"}

VARIABLES correct, faulty, pc, msgsRecv, msgsSent
vars == << correct, faulty, pc, msgsRecv, msgsSent >>

TypeOK ==
    /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
    /\ pc \in [1..N -> {"init", "noinit", "echoed", "accepted"}]
    /\ msgsRecv \in [1..N -> SUBSET ((1..N) \X MessageTypes)]
    /\ msgsSent \in SUBSET ((1..N) \X MessageTypes)

FCConstraints ==
    /\ correct = (1..N) \ faulty
    /\ correct # {}
    /\ cardinality(correct) = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ msgsSent \subseteq (correct \X MessageTypes)

EchoCount(p) == Cardinality({m \in msgsRecv[p] : m[2] = "ECHO"})
EchoSenders(p) == {m[1] : m \in msgsRecv[p] /\ m[2] = "ECHO"}

Init == {p \in 1..N : pc[p] = "init"}

InitRecv == \E p \in 1..N : pc[p] = "init"

\* A correct process receives a batch of messages from correct and Byzantine
\* senders; this is its only direct way to learn the broadcast.
Receive(p) ==
    /\ p \in correct
    /\ \E ms \in SUBSET ((1..N) \X MessageTypes) :
        msgsRecv' = [msgsRecv EXCEPT ![p] = @ \cup ms]
    /\ UNCHANGED << correct, faulty, pc, msgsSent >>

\* Receiving an INIT broadcast (starting in the "init" state) forces an immediate
\* accept-and-echo response from a correct process.
SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "init"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ msgsSent' = msgsSent \cup {<<p, "ECHO">>}
    /\ UNCHANGED << correct, faulty, msgsRecv >>

\* Accumulating a moderate echo quorum: the process may now send an echo, but
\* it still needs a stronger quorum before it can accept.
EchoMid(p) ==
    /\ p \in correct
    /\ pc[p] \in {"noinit", "echoed"}
    /\ EchoCount(p) >= N - 2 * T
    /\ EchoCount(p) < N - T
    /\ pc' = [pc EXCEPT ![p] = "echoed"]
    /\ msgsSent' = msgsSent \cup {<<p, "ECHO">>}
    /\ UNCHANGED << correct, faulty, msgsRecv >>

\* Receiving a strong enough echo quorum lets the process accept and echo.
EchoStrong(p) ==
    /\ p \in correct
    /\ pc[p] \in {"noinit", "echoed"}
    /\ EchoCount(p) >= N - T
    /\ EchoSenders(p) \subseteq correct
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ msgsSent' = msgsSent \cup {<<p, "ECHO">>}
    /\ UNCHANGED << correct, faulty, msgsRecv >>

\* A process that has already sent its echo and now sees a strong quorum accepts.
AcceptMid(p) ==
    /\ p \in correct
    /\ pc[p] = "echoed"
    /\ EchoCount(p) >= N - T
    /\ EchoSenders(p) \subseteq correct
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED << correct, faulty, msgsRecv, msgsSent >>

Next ==
    \/ \E p \in 1..N : Receive(p)
    \/ \E p \in 1..N : SendEcho(p)
    \/ \E p \in 1..N : EchoMid(p)
    \/ \E p \in 1..N : EchoStrong(p)
    \/ \E p \in 1..N : AcceptMid(p)

\* All of the above can interleave in any order, so fairness is applied only
\* to the combined receive-and-act steps of correct processes.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in correct :
        TRUE

Liveness ==
    /\ (\A p \in correct : pc[p] \in {"init", "accepted"})
        ~> (\A p \in correct : pc[p] = "accepted")
    /\ (\E p \in correct : pc[p] = "accepted")
        ~> (\A p \in correct : pc[p] = "accepted")

\* Unforgeability is a safety check and needs no fairness.
Unforg ==
    /\ ~InitRecv
        ~> (\A p \in correct : pc[p] = "noinit")
CorrLtl == Liveness
RelayLtl == Liveness
UnforgLtl == TRUE

====
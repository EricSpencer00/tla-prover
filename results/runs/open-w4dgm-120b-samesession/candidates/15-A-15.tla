---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, rxs, sent

InitLocs == {"initrcvd", "initabs"}
ProgLocs == {"echoSent", "accepted"}

TypeOK ==
    /\ correct \subseteq 1..N
    /\ faulty \subseteq 1..N
    /\ loc \in [1..N -> (InitLocs \cup ProgLocs) \cup {"initabs"}]
    /\ rxs \in [1..N -> SUBSET (1..N \X {"ECHO"})]
    /\ sent \in SUBSET (1..N)

SentBy(i) == {p \in 1..N : <<i, "ECHO">> \in sent}

Init ==
    /\ correct = {i \in 1..N : i <= (N - F)}
    /\ faulty = {i \in 1..N : i > (N - F)}
    /\ loc = [i \in 1..N |-> IF i <= (N - F) THEN "initrcvd" ELSE "initabs"]
    /\ rxs = [i \in 1..N |-> {}]
    /\ sent = {}

InitNoBroad ==
    /\ correct = {i \in 1..N : i <= (N - F)}
    /\ faulty = {i \in 1..N : i > (N - F)}
    /\ loc = [i \in 1..N |-> "initabs"]
    /\ rxs = [i \in 1..N |-> {}]
    /\ sent = {}

RecvMsg(i) ==
    /\ loc[i] \in InitLocs
    /\ \E S \in SUBSET (SentBy(0) \cup faulty):
         rxs' = [rxs EXCEPT ![i] = @ \cup S]
    /\ UNCHANGED <<correct, faulty, loc, sent>>

BroadcastEcho(i) ==
    /\ loc[i] \in InitLocs
    /\ loc' = [loc EXCEPT ![i] = "echoSent"]
    /\ sent' = sent \cup {<<i, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rxs>>

SendEchoOnQuorum(i) ==
    /\ loc[i] = "initrcvd"
    /\ Cardinality(rxs[i]) >= N - 2 * T
    /\ Cardinality(rxs[i]) < N - T
    /\ loc' = [loc EXCEPT ![i] = "echoSent"]
    /\ sent' = sent \cup {<<i, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rxs>>

AcceptOnQuorum(i) ==
    /\ loc[i] = "initrcvd"
    /\ Cardinality(rxs[i]) >= N - T
    /\ loc' = [loc EXCEPT ![i] = "accepted"]
    /\ sent' = sent \cup {<<i, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, rxs>>

AcceptLate(i) ==
    /\ loc[i] = "echoSent"
    /\ Cardinality(rxs[i]) >= N - T
    /\ loc' = [loc EXCEPT ![i] = "accepted"]
    /\ UNCHANGED <<correct, faulty, rxs, sent>>

Next ==
    \/ Init \/ InitNoBroad
    \/ \E i \in 1..N:
         \/ RecvMsg(i) \/ BroadcastEcho(i) \/ SendEchoOnQuorum(i)
         \/ AcceptOnQuorum(i) \/ AcceptLate(i)

Spec ==
    /\ Init
    /\ [][Next]_<<correct, faulty, loc, rxs, sent>>
    /\ SF_vars(\E i \in 1..N: RecvMsg(i))
    /\ SF_vars(\E i \in 1..N: BroadcastEcho(i))
    /\ SF_vars(\E i \in 1..N: SendEchoOnQuorum(i))
    /\ SF_vars(\E i \in 1..N: AcceptOnQuorum(i))
    /\ SF_vars(\E i \in 1..N: AcceptLate(i))

CorrLtl ==
    (correct # {}) => (\A i \in correct : <>(loc[i] \in ProgLocs))

RelayLtl ==
    (\E i \in correct : loc[i] = "accepted") ~> (\A i \in correct : loc[i] \in ProgLocs)

FCConstraints ==
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = 1..N
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

UnforgLtl ==
    (\A i \in correct : loc[i] \in InitLocs) ~> (\A i \in correct : loc[i] \in ProgLocs)

====
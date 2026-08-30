---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

Locs == {"broadcast", "nobroadcast", "sbroadcast", "accepted"}
Msgs == {"echo", "init"}

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ pc \in [1..N -> Locs]
    /\ recv \in [1..N -> SUBSET (Msgs \X (1..N))]
    /\ sent \subseteq (Msgs \X (1..N))

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ correct \cap faulty = {}
    /\ correct \cup faulty = 1..N
    /\ Cardinality(correct) = N - F

Init ==
    /\ correct = {c \in 1..N : c > F}
    /\ faulty = {c \in 1..N : c <= F}
    /\ (N - F) >= 1
    /\ pc = [c \in 1..N |-> IF c > F THEN "broadcast" ELSE "nobroadcast"]
    /\ recv = [c \in 1..N |-> {}]
    /\ sent = {}

InitNoBroadcast ==
    /\ correct = {c \in 1..N : c > F}
    /\ faulty = {c \in 1..N : c <= F}
    /\ (N - F) >= 1
    /\ pc = [c \in 1..N |-> "nobroadcast"]
    /\ recv = [c \in 1..N |-> {}]
    /\ sent = {}

Deliver(c) ==
    /\ c \in correct
    /\ recv' = [recv EXCEPT ![c] = recv[c] \cup
                    {m \in sent : m \in (Msgs \X correct) \cup (Msgs \X faulty)}]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

BroadcastInit(c) ==
    /\ c \in correct
    /\ pc[c] = "broadcast"
    /\ pc' = [pc EXCEPT ![c] = "accepted"]
    /\ sent' = sent \cup {<<"echo", c>>}
    /\ recv' = [recv EXCEPT ![c] = recv[c] \cup {<<"init", c>>}]
    /\ UNCHANGED <<correct, faulty>>

RelayExact(c) ==
    /\ c \in correct
    /\ pc[c] \notin {"accepted", "sbroadcast"}
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) >= N - T
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) < N - 2 * T
    /\ pc' = [pc EXCEPT ![c] = "sbroadcast"]
    /\ sent' = sent \cup {<<"echo", c>>}
    /\ UNCHANGED <<correct, faulty, recv>>

RelayFaster(c) ==
    /\ c \in correct
    /\ pc[c] \notin {"accepted", "sbroadcast"}
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) >= N - 2 * T
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) < N - T
    /\ pc' = [pc EXCEPT ![c] = "sbroadcast"]
    /\ sent' = sent \cup {<<"echo", c>>}
    /\ UNCHANGED <<correct, faulty, recv>>

RelaySlow(c) ==
    /\ c \in correct
    /\ pc[c] \notin {"accepted", "sbroadcast"}
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) >= N - T
    /\ pc' = [pc EXCEPT ![c] = "accepted"]
    /\ sent' = sent \cup {<<"echo", c>>}
    /\ UNCHANGED <<correct, faulty, recv>>

RelayFinished(c) ==
    /\ c \in correct
    /\ pc[c] = "sbroadcast"
    /\ Cardinality(recv[c] \cap (Msgs \X correct)) >= N - T
    /\ pc' = [pc EXCEPT ![c] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
    \/ \E c \in 1..N : Deliver(c) \/ BroadcastInit(c) \/ RelayExact(c)
                         \/ RelayFaster(c) \/ RelaySlow(c) \/ RelayFinished(c)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E c \in 1..N : Deliver(c))
    /\ WF_vars(\E c \in 1..N : RelayExact(c) \/ RelayFaster(c) \/ RelaySlow(c))
    /\ WF_vars(\E c \in 1..N : RelayFinished(c))

CorrLtl == <>(\A c \in correct : pc[c] = "accepted")
RelayLtl == (\E c \in correct : pc[c] = "accepted") ~> (\A c \in correct : pc[c] = "accepted")
UnforgLtl == (\A c \in correct : pc[c] = "nobroadcast") ~> (\A c \in correct : pc[c] # "accepted")
====
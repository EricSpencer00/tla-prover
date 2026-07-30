---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

RECURSIVE NatPred(_, _)
NatPred(n, k) ==
    IF k = 0 THEN n = n
    ELSE IF n = 0 THEN TRUE
    ELSE NatPred(n - 1, k - 1)

VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

CorrectSet == { k \in 1..N : k \notin faulty }

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc \in [1..N -> {"startBroad", "startQuiet", "echoed", "accepted"}]
    /\ recv \in [1..N -> SUBSET [snd: 1..N, tag: {"echo"}]]
    /\ sent \subseteq [snd: 1..N, tag: {"echo"}]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

Init ==
    /\ \E pc1 \in {"startBroad", "startQuiet"}:
         /\ \E pc2 \in {"startBroad", "startQuiet"}:
              /\ \E pc3 \in {"startBroad", "startQuiet"}:
                   /\ \E pc4 \in {"startBroad", "startQuiet"}:
                        /\ pc = [k \in 1..N |-> CASE k = 1 -> pc1 [] k = 2 -> pc2 [] k = 3 -> pc3 [] k = 4 -> pc4]
         /\ Cardinality({ k \in 1..N : pc[k] = "startBroad" }) = N - F
    /\ recv = [k \in 1..N |-> {}]
    /\ sent = {}

ByzNoise(i) == { [snd |-> f, tag |-> "echo"] : f \in faulty }

Receive(i) ==
    /\ i \in correct
    /\ pc[i] \notin {"echoed", "accepted"}
    /\ \E msgs \in SUBSET (sent \cup ByzNoise(i)):
         /\ recv' = [recv EXCEPT ![i] = msgs]
    /\ UNCHANGED << correct, faulty, pc, sent >>

EchoAndAccept(i) ==
    /\ i \in correct
    /\ pc[i] = "startBroad"
    /\ pc' = [pc EXCEPT ![i] = "accepted"]
    /\ sent' = sent \cup {[snd |-> i, tag |-> "echo"]}
    /\ UNCHANGED << correct, faulty, recv >>

EchoOnly(i) ==
    /\ i \in correct
    /\ pc[i] = "startQuiet"
    /\ Cardinality(recv[i]) >= N - 2 * T
    /\ Cardinality(recv[i]) < N - T
    /\ pc' = [pc EXCEPT ![i] = "echoed"]
    /\ sent' = sent \cup {[snd |-> i, tag |-> "echo"]}
    /\ UNCHANGED << correct, faulty, recv >>

EchoAndAcceptQuorum(i) ==
    /\ i \in correct
    /\ pc[i] = "startQuiet"
    /\ Cardinality(recv[i]) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "accepted"]
    /\ sent' = sent \cup {[snd |-> i, tag |-> "echo"]}
    /\ UNCHANGED << correct, faulty, recv >>

AcceptQuorum(i) ==
    /\ i \in correct
    /\ pc[i] = "echoed"
    /\ Cardinality(recv[i]) >= N - T
    /\ pc' = [pc EXCEPT ![i] = "accepted"]
    /\ UNCHANGED << correct, faulty, recv, sent >>

Next ==
    \/ \E i \in 1..N: Receive(i)
    \/ \E i \in 1..N: EchoAndAccept(i)
    \/ \E i \in 1..N: EchoOnly(i)
    \/ \E i \in 1..N: EchoAndAcceptQuorum(i)
    \/ \E i \in 1..N: AcceptQuorum(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E i \in 1..N: EchoAndAccept(i))
    /\ WF_vars(\E i \in 1..N: EchoOnly(i))

CorrLtl == <>(\A i \in correct: pc[i] = "accepted")

RelayLtl ==
    /\ (\E i \in correct: pc[i] = "accepted") ~> (\A i \in correct: pc[i] = "accepted")

UnforgLtl ==
    /\ (\A i \in correct: pc[i] = "startQuiet") ~> (\A i \in correct: pc[i] = "startQuiet")

====
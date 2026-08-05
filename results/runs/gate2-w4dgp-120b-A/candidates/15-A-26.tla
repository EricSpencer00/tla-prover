---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

Reachable(s) == {x : x \in s}
Ids == 0..(N - 1)
ReceivedBy(p) == {m \in recv[p] : m[2] = "echo"}
EchoSenders(p) == {m[1] : m \in ReceivedBy(p)}

InitState == IF (Rq \in Reachable(Ids)) THEN "hasinit" ELSE "noinit"
RestrictedInit == IF (Rq \in Reachable(Ids)) THEN "noinit" ELSE "hasinit"

Init ==
    /\ correct \in {S \in SUBSET Ids : Cardinality(S) = N - F}
    /\ faulty = Ids \ correct
    /\ pc \in [Ids -> {"hasinit", "noinit", "sent", "accepted"}]
    /\ recv \in [Ids -> SUBSET (Ids \X {"echo"})]
    /\ sent \in [Ids -> SUBSET (Ids \X {"echo"})]

ReceiveMessages(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"sent", "accepted"}
    /\ \E m \in SUBSET (sent[RECURSIVE f \in correct : f] \cup (faulty \X {"echo"})) :
        /\ recv' = [recv EXCEPT ![p] = @ \cup m]
        /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"sent", "accepted"}
    /\ Cardinality(EchoSenders(p)) >= N - T
    /\ sent' = [sent EXCEPT ![p] = Ids \X {"echo"}]
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, recv>>

AcceptWithEcho(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"accepted"}
    /\ Cardinality(EchoSenders(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

AcceptLate(p) ==
    /\ p \in correct
    /\ pc[p] \notin {"accepted"}
    /\ N - 2 * T <= Cardinality(EchoSenders(p))
    /\ Cardinality(EchoSenders(p)) < N - T
    /\ sent' = [sent EXCEPT ![p] = Ids \X {"echo"}]
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, recv>>

AcceptBroadcast(p) ==
    /\ p \in correct
    /\ pc[p] = "hasinit"
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ sent' = [sent EXCEPT ![p] = Ids \X {"echo"}]
    /\ UNCHANGED <<correct, faulty, recv>>

Next ==
    \/ \E p \in Ids : ReceiveMessages(p) \/ SendEcho(p) \/ AcceptBroadcast(p) \/ AcceptLate(p) \/ AcceptWithEcho(p)
    \/ UNCHANGED vars

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E p \in correct : ReceiveMessages(p))
    /\ WF_vars(\E p \in correct : SendEcho(p))
    /\ WF_vars(\E p \in correct : AcceptWithEcho(p))

SpecNoFairness == Init /\ [][Next]_vars

TypeOK ==
    /\ correct \subseteq Ids
    /\ faulty = Ids \ correct
    /\ pc \in [Ids -> {"hasinit", "noinit", "sent", "accepted"}]
    /\ \A p \in Ids : recv[p] \subseteq (Ids \X {"echo"})
    /\ \A p \in Ids : sent[p] \subseteq (Ids \X {"echo"})

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

UnforgLtl == (InitState = "noinit") ~> (\A p \in correct : pc[p] # "accepted")
CorrLtl == (InitState = "hasinit") ~> (\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

====
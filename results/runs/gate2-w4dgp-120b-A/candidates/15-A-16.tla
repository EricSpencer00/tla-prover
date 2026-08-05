---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N >= 1 /\ T >= 1 /\ T >= F

MessageTypes == {"init", "echo"}

VARIABLES correct, faulty, pc, recv, sent
vars == <<correct, faulty, pc, recv, sent>>

RECURSIVE SSum(_)
SSum(S) == LET x == CHOOSE y \in S : TRUE
               T == S \ {x}
           IN IF T = {} THEN {x} ELSE {x} \cup SSum(T)

RECURSIVE FoldUnion(_)
FoldUnion(r) == LET f[S \in SUBSET SSum(r)] ==
                    IF S = {} THEN {}
                    ELSE LET x == CHOOSE y \in S : TRUE
                         IN {x} \cup f[S \ {x}]
                IN f[r]

Messages == {<<n, mtype>> : n \in 1..N, mtype \in MessageTypes}

TypeOK ==
    /\ correct \subseteq 1..N
    /\ cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc \in [1..N -> {"noinit", "init", "sent", "accepted"}]
    /\ recv \in [1..N -> SUBSET Messages]
    /\ sent \in SUBSET Messages

Init ==
    /\ correct = CHOOSE S \in FoldUnion(1..N) : cardinality(S) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> IF p \in correct THEN "init" ELSE "noinit"]
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = {}

InitNoBroadcast ==
    /\ correct = CHOOSE S \in FoldUnion(1..N) : cardinality(S) = N - F
    /\ faulty = (1..N) \ correct
    /\ pc = [p \in 1..N |-> "noinit"]
    /\ recv = [p \in 1..N |-> {}]
    /\ sent = {}

InitSet == Init \/ InitNoBroadcast

Receive(p, S) ==
    /\ p \in correct
    /\ S \subseteq sent \cup {<<q, "echo">> : q \in faulty}
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup S]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
    /\ pc[p] = "init"
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, recv>>

RelaySend(p) ==
    /\ pc[p] # "init"
    /\ pc[p] # "accepted"
    /\ p \in correct
    /\ Cardinality({q \in correct : <<q, "echo">> \in recv[p]}) >= N - 2 * T
    /\ Cardinality({q \in correct : <<q, "echo">> \in recv[p]}) < N - T
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "sent"]
    /\ UNCHANGED <<correct, faulty, recv>>

RelayAccept(p) ==
    /\ pc[p] # "init"
    /\ pc[p] # "accepted"
    /\ Cardinality({q \in correct : <<q, "echo">> \in recv[p]}) >= N - T
    /\ sent' = sent \cup {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recv>>

RelayAcceptOnly(p) ==
    /\ pc[p] = "sent"
    /\ Cardinality({q \in correct : <<q, "echo">> \in recv[p]}) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
    \/ \E p \in 1..N, S \in SUBSET Messages : Receive(p, S)
    \/ \E p \in 1..N : SendEcho(p) \/ RelaySend(p) \/ RelayAccept(p) \/ RelayAcceptOnly(p)

Spec ==
    /\ InitSet
    /\ [][Next]_vars
    /\ WF_vars(\E p \in 1..N, S \in SUBSET Messages : Receive(p, S))
    /\ WF_vars(\E p \in 1..N : SendEcho(p))
    /\ WF_vars(\E p \in 1..N : RelaySend(p))
    /\ WF_vars(\E p \in 1..N : RelayAccept(p) \/ RelayAcceptOnly(p))

UnforgLtl ==
    \A p \in correct : (pc[p] = "init") ~> (pc[p] = "accepted")
    /\ \A p \in correct : (pc[p] = "noinit") ~> (pc[p] = "noinit")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accepted")

RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====
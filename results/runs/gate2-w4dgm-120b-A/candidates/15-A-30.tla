---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, inbox, sent

vars == <<correct, faulty, pc, inbox, sent>>

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ pc \in [1..N -> {"init", "nobro", "echosent", "accept"}]
    /\ inbox \in [1..N -> SUBSET (1..N \X {"echo"})]
    /\ sent \subseteq (1..N \X {"echo"})

Init ==
    /\ Cardinality(correct) = N - F
    /\ faulty = (1..N) \ correct
    /\ sent = {}
    /\ inbox = [p \in 1..N |-> {}]
    /\ \E initMask \in SUBSET (1..N) :
         pc = [p \in 1..N |-> IF p \in initMask THEN "init" ELSE "nobro"]

ReceiveMsgs(p) ==
    /\ p \in correct
    /\ pc[p] \in {"init", "nobro"}
    /\ \E m \in SUBSET (sent \union (faulty \X {"echo"})) :
         inbox' = [inbox EXCEPT ![p] = inbox[p] \union m]
    /\ UNCHANGED <<correct, faulty, pc, sent>>

InitAcceptEcho(p) ==
    /\ p \in correct
    /\ pc[p] = "init"
    /\ sent' = sent \union {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<correct, faulty, inbox>>

EchoIfAboveN2T(p) ==
    /\ p \in correct
    /\ pc[p] = "nobro"
    /\ Cardinality(inbox[p]) >= N - 2 * T
    /\ Cardinality(inbox[p]) < N - T
    /\ sent' = sent \union {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "echosent"]
    /\ UNCHANGED <<correct, faulty, inbox>>

EchoIfAboveNT(p) ==
    /\ p \in correct
    /\ pc[p] = "nobro"
    /\ Cardinality(inbox[p]) >= N - T
    /\ sent' = sent \union {<<p, "echo">>}
    /\ pc' = [pc EXCEPT ![p] = "echosent"]
    /\ UNCHANGED <<correct, faulty, inbox>>

AcceptIfAboveNT(p) ==
    /\ p \in correct
    /\ pc[p] = "echosent"
    /\ Cardinality(inbox[p]) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "accept"]
    /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
    \/ \E p \in 1..N : ReceiveMsgs(p)
    \/ \E p \in 1..N : InitAcceptEcho(p)
    \/ \E p \in 1..N : EchoIfAboveN2T(p)
    \/ \E p \in 1..N : EchoIfAboveNT(p)
    \/ \E p \in 1..N : AcceptIfAboveNT(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in 1..N : WF_vars(ReceiveMsgs(p))

UnforgLtl == (\A p \in correct : pc[p] = "nobro") ~> (\A p \in correct : pc[p] = "accept")

CorrLtl == (\A p \in correct : pc[p] = "init") ~> (\A p \in correct : pc[p] = "accept")

RelayLtl == (\E p \in correct : pc[p] = "accept") ~> (\A p \in correct : pc[p] = "accept")

FCConstraints ==
    /\ N \in Nat /\ T \in Nat /\ F \in Nat
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

====
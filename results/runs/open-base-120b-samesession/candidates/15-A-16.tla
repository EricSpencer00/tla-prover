---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

(* --------------------------------------------------------------------- *)
(* Process universe *)
Proc == 1..N

(* --------------------------------------------------------------------- *)
(* Variables *)
VARIABLES correct, initRecv, echoSent, accepted, rec

vars == <<correct, initRecv, echoSent, accepted, rec>>

(* Derived sets *)
Faulty == Proc \ correct
SentSet == {p \in correct : echoSent[p]}

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ initRecv \in [Proc -> BOOLEAN]
    /\ echoSent = [p \in Proc |-> FALSE]
    /\ accepted = [p \in Proc |-> FALSE]
    /\ rec = [p \in Proc |-> {}]

(* --------------------------------------------------------------------- *)
(* Actions *)

Receive(p, new) ==
    /\ p \in correct
    /\ new \subseteq (SentSet \cup Faulty) \ rec[p]
    /\ rec' = [rec EXCEPT ![p] = @ \cup new]
    /\ UNCHANGED <<correct, initRecv, echoSent, accepted>>

InitAccept(p) ==
    /\ p \in correct
    /\ initRecv[p] = TRUE
    /\ ~echoSent[p]
    /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<correct, initRecv, rec>>

EchoCond1(p) ==
    /\ p \in correct
    /\ ~echoSent[p]
    /\ Cardinality(rec[p]) >= N - 2*T
    /\ Cardinality(rec[p]) < N - T
    /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<correct, initRecv, accepted, rec>>

EchoCond2(p) ==
    /\ p \in correct
    /\ ~echoSent[p]
    /\ Cardinality(rec[p]) >= N - T
    /\ echoSent' = [echoSent EXCEPT ![p] = TRUE]
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<correct, initRecv, rec>>

AcceptAfterEcho(p) ==
    /\ p \in correct
    /\ echoSent[p] = TRUE
    /\ ~accepted[p]
    /\ Cardinality(rec[p]) >= N - T
    /\ accepted' = [accepted EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<correct, initRecv, echoSent, rec>>

Next ==
    \/ \E p \in correct: \E new \subseteq (SentSet \cup Faulty) \ rec[p] : Receive(p, new)
    \/ \E p \in correct: InitAccept(p)
    \/ \E p \in correct: EchoCond1(p)
    \/ \E p \in correct: EchoCond2(p)
    \/ \E p \in correct: AcceptAfterEcho(p)

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ initRecv \in [Proc -> BOOLEAN]
    /\ echoSent \in [Proc -> BOOLEAN]
    /\ accepted \in [Proc -> BOOLEAN]
    /\ rec \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : rec[p] \subseteq Proc
    /\ \A p \in Proc : (p \notin correct) => (echoSent[p] = FALSE /\ accepted[p] = FALSE)

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0
    /\ Cardinality(correct) = N - F

(* --------------------------------------------------------------------- *)
(* LTL properties *)

CorrLtl == ( \A p \in correct : initRecv[p] ) => <> ( \A p \in correct : accepted[p] )

RelayLtl == ( \E p \in correct : accepted[p] ) => <> ( \A p \in correct : accepted[p] )

UnforgLtl == ( \A p \in correct : ~initRecv[p] ) => [] ( \A p \in correct : ~accepted[p] )

====
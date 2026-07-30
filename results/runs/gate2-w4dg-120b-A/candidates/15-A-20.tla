---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ControlNames == {"noinit", "haveinit", "sent", "accepted"}
Msgs == [from: 1..N, kind: {"ECHO"}]

VARIABLES correct, faulty, loc, received, sent

vars == <<correct, faulty, loc, received, sent>>

EchoesFrom(p) == {m.from : m \in {x \in received[p] : x.kind = "ECHO"}}

TypeOK ==
    /\ correct \subseteq (1..N)
    /\ faulty \subseteq (1..N)
    /\ loc \in [1..N -> ControlNames]
    /\ received \in [1..N -> SUBSET Msgs]
    /\ sent \in SUBSET Msgs

FCConstraints ==
    /\ correct \cup faulty = (1..N)
    /\ correct \cap faulty = {}
    /\ Cardinality(correct) = N - F
    /\ \A p \in 1..N : loc[p] \in ControlNames

Init ==
    /\ \E ic \in {0, 1} :
         /\ ic = 0 => \A p \in 1..N : loc[p] = "noinit"
         /\ ic = 1 => \E S \in SUBSET (1..N) :
              /\ S \neq {} /\ S # (1..N)
              /\ \A p \in 1..N : loc[p] = (IF p \in S THEN "haveinit" ELSE "noinit")
    /\ correct \cup faulty = (1..N)
    /\ \E C \in SUBSET (1..N) :
         /\ Cardinality(C) = N - F
         /\ correct = C
    /\ received = [p \in 1..N |-> {}]
    /\ sent = {}

RecieveStep(p) ==
    /\ loc[p] \in {"noinit", "haveinit"}
    /\ \E news \in SUBSET (sent \cup Msgs) :
         received' = [received EXCEPT ![p] = @ \cup news]
    /\ UNCHANGED <<correct, faulty, loc, sent>>

BroadcastEcho(p) ==
    /\ loc[p] = "haveinit"
    /\ loc' = [loc EXCEPT ![p] = "sent"]
    /\ sent' = sent \cup {[from |-> p, kind |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, received>>

EchoWithAssist(p) ==
    /\ loc[p] = "noinit"
    /\ loc[p] \notin {"sent", "accepted"}
    /\ Cardinality(EchoesFrom(p)) >= N - 2 * T
    /\ Cardinality(EchoesFrom(p)) < N - T
    /\ loc' = [loc EXCEPT ![p] = "sent"]
    /\ sent' = sent \cup {[from |-> p, kind |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, received>>

EchoWithAccept(p) ==
    /\ loc[p] = "noinit"
    /\ loc[p] \notin {"sent", "accepted"}
    /\ Cardinality(EchoesFrom(p)) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "sent"]
    /\ sent' = sent \cup {[from |-> p, kind |-> "ECHO"]}
    /\ UNCHANGED <<correct, faulty, received>>

LateAccept(p) ==
    /\ loc[p] = "sent"
    /\ loc[p] \notin {"accepted"}
    /\ Cardinality(EchoesFrom(p)) >= N - T
    /\ loc' = [loc EXCEPT ![p] = "accepted"]
    /\ UNCHANGED <<correct, faulty, received, sent>>

CorrectStep == \E p \in correct :
    \/ RecieveStep(p)
    \/ BroadcastEcho(p)
    \/ EchoWithAssist(p)
    \/ EchoWithAccept(p)
    \/ LateAccept(p)

Next == CorrectStep

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CorrectStep)
        /\ SF_vars(RecieveStep(1))

CorrLtl == (EF \A p \in correct : loc[p] = "haveinit")
           ~> (EF \A p \in correct : loc[p] = "accepted")

RelayLtl == (EF \E p \in correct : loc[p] = "accepted")
            ~> (EF \A p \in correct : loc[p] = "accepted")

UnforgLtl == (EF \A p \in correct : loc[p] = "noinit")
              ~> (EF \A p \in correct : loc[p] # "accepted")
====
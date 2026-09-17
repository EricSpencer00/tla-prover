---- MODULE 22_simple_election ----
\* benchmark: ex-simple-election

EXTENDS TLC, FiniteSetTheorems, TLAPS

CONSTANT Acceptor
CONSTANT Quorum
CONSTANT Proposer

VARIABLE start
VARIABLE promise
VARIABLE leader

vars == <<start,promise,leader>>

DidNotPromise(a) == \A p \in Proposer : <<a,p>> \notin promise
ChosenAt(Q, p) == \A a \in Q : <<a,p>> \in promise

\*
\* Actions.
\*

Send1a(p) ==
    /\ start' = start \cup {p}
    /\ UNCHANGED <<promise,leader>>

Send1b(a, p) ==
    /\ p \in start
    /\ DidNotPromise(a)
    /\ promise' = promise \cup {<<a,p>>}
    /\ UNCHANGED <<start, leader>>

Decide(p, Q) ==
    /\ ChosenAt(Q, p)
    /\ leader' = leader \cup {p}
    /\ UNCHANGED <<start, promise>>

Next ==
    \/ \E p \in Proposer : Send1a(p)
    \/ \E a \in Acceptor, p \in Proposer : Send1b(a, p)
    \/ \E p \in Proposer : \E Q \in Quorum : Decide(p, Q)

Init ==
    /\ start = {}
    /\ promise = {}
    /\ leader = {}

NextUnchanged == UNCHANGED vars

TypeOK ==
    /\ start \in SUBSET Proposer
    /\ promise \in SUBSET (Acceptor \X Proposer)
    /\ leader \in SUBSET Proposer

Safety == \A pi,pj \in Proposer : (pi \in leader /\ pj \in leader) => (pi = pj)

\* Inductive strengthening conjuncts
Inv219_1_0_def == \A VARS \in Acceptor : \A VARPA \in Proposer : (VARPA \in start) \/ (~(<<VARS,VARPA>> \in promise))
Inv136_1_1_def == \A VARPA \in Proposer : \E VARQ \in Quorum : (ChosenAt(VARQ,VARPA)) \/ (~(VARPA \in leader))
Inv200_2_2_def == \A VARS \in Acceptor : \A VARPA \in Proposer : \A VARPB \in Proposer : ((VARPA=VARPB) /\ promise = promise) \/ (~(<<VARS,VARPA>> \in promise)) \/ (~(<<VARS,VARPB>> \in promise))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv219_1_0_def
  /\ Inv136_1_1_def
  /\ Inv200_2_2_def


ASSUME QuorumsNonEmpty == Quorum # {}
ASSUME Fin == IsFiniteSet(Acceptor) /\ IsFiniteSet(Proposer)
ASSUME QuorumsType == Quorum \subseteq SUBSET Acceptor
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
ASSUME NonEmpty == Proposer # {}


THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY SMT
====
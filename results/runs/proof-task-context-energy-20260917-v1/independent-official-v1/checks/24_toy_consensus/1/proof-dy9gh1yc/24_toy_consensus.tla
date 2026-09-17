---- MODULE 24_toy_consensus ----
\* benchmark: ex-toy-consensus

EXTENDS TLC, FiniteSets, Naturals, FiniteSetTheorems

CONSTANT Node
CONSTANT Value
CONSTANT Nil

VARIABLE vote
VARIABLE decision

vars == <<vote,decision>>

Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

ChosenAt(v, Q) == \A m \in Q : vote[m] = v

\* Node i casts vote for value 'v'.
CastVote(i, v) ==
    /\ vote[i] = Nil
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ UNCHANGED decision
    
\* Decide on value 'v' with quorum 'Q'.
Decide(v, Q) ==
    /\ ChosenAt(v, Q)
    /\ decision' = decision \cup {v}
    /\ UNCHANGED vote

Init == 
    /\ vote = [n \in Node |-> Nil]
    /\ decision = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorums : Decide(v, Q)

TypeOK == 
    /\ vote \in [Node -> Value \cup {Nil}]
    /\ decision \in SUBSET Value

NextUnchanged == UNCHANGED vars

\* At most one value is decided upon.
Inv == \A vi, vj \in decision : vi = vj

Symmetry == Permutations(Node) \cup Permutations(Value)

\* Inductive strengthening conjuncts
Inv78_1_0_def == \A VARI \in Node : \A VARJ \in Node : \A VARV \in Value : \A VARQ \in Quorums : \E VART \in VARQ :(vote[VART] = VARV) \/ (~(VARV \in decision))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv78_1_0_def

ASSUME QuorumType == Quorums \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorums : Q # {}
ASSUME QuorumsExist == Quorums # {}
ASSUME ValueNonEmpty == Value # {}
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME NilType == Nil \notin Node /\ Nil \notin Value

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY DEF vars, Quorums, ChosenAt, CastVote, Decide, Init, Next, TypeOK, NextUnchanged, Inv, Symmetry, Inv78_1_0_def, IndAuto
====
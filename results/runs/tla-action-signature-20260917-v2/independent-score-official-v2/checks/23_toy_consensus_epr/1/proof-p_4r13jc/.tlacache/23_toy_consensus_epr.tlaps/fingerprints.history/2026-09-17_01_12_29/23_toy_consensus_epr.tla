---- MODULE 23_toy_consensus_epr ----
\* benchmark: pyv-toy-consensus-epr

EXTENDS TLC, Naturals, FiniteSets, FiniteSetTheorems

CONSTANT Node
CONSTANT Quorum
CONSTANT Value

VARIABLE voted
VARIABLE vote
VARIABLE decided

vars == <<voted,vote,decided>>

ChosenAt(Q, v) == \A n \in Q : <<n,v>> \in vote

\* Node 'i' casts a vote for value 'v'.
CastVote(n, v) == 
    /\ n \notin voted
    /\ vote' = vote \cup {<<n,v>>}
    /\ voted' = voted \cup {n}
    /\ UNCHANGED <<decided>>

\* Decide on a value 'v' with quorum 'Q'.
Decide(v, Q) == 
    /\ ChosenAt(Q, v)
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<vote,voted>>

Init ==
    /\ voted = {}
    /\ vote = {}
    /\ decided = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorum : Decide(v, Q)

NextUnchanged == UNCHANGED vars

TypeOK == 
    /\ voted \in SUBSET Node
    /\ vote \in SUBSET (Node \X Value)
    /\ decided \in SUBSET Value

\* Can only decide on a single value
Safety == \A vi,vj \in decided : vi = vj

Symmetry == Permutations(Node) \cup Permutations(Value)

\* Inductive strengthening conjuncts
Inv220_1_0_def == \A VARS \in Node : \A VARA \in Value : (VARS \in voted) \/ (~(<<VARS,VARA>> \in vote))
Inv155_1_1_def == \E VARQ \in Quorum : \A VARA \in Value : (ChosenAt(VARQ, VARA)) \/ (~(VARA \in decided))
Inv201_2_2_def == \A VARS \in Node : \A VARA \in Value : \A VARB \in Value : ((VARA = VARB) /\ vote = vote) \/ (~(<<VARS,VARA>> \in vote)) \/ (~(<<VARS,VARB>> \in vote))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv220_1_0_def
  /\ Inv155_1_1_def
  /\ Inv201_2_2_def

ASSUME QuorumType == Quorum \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorum : Q # {}
ASSUME QuorumsExist == Quorum # {}
ASSUME ValueNonEmpty == Value # {}
ASSUME NodeNonEmpty == Node # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}


THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY DEF vars, ChosenAt, CastVote, Decide, Init, Next, NextUnchanged, TypeOK, Safety, Symmetry, Inv220_1_0_def, Inv155_1_1_def, Inv201_2_2_def, IndAuto
====
---- MODULE 5_toy_consensus_forall ----
\* benchmark: pyv-toy-consensus-forall

EXTENDS TLC, Naturals, FiniteSets, FiniteSetTheorems

CONSTANT Node
CONSTANT Value
CONSTANT Nil

VARIABLE vote
VARIABLE voted
VARIABLE decided

vars == <<vote, voted, decided>>

\* The set of all majority quorums in the Node set.
Quorums == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

\* Node 'i' casts a vote for value 'v'.
CastVote(i, v) == 
    /\ ~voted[i]
    /\ vote' = [vote EXCEPT ![i] = v]
    /\ voted' = [voted EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<decided>>

\* Decide on a value 'v' with quorum 'Q'.
Decide(v, Q) == 
    /\ \A n \in Q : vote[n] = v
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<vote,voted>>

Init ==
    /\ vote = [n \in Node |-> Nil]
    /\ voted = [n \in Node |-> FALSE]
    /\ decided = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorums : Decide(v, Q)

NextUnchanged == UNCHANGED vars

\* Can only decide on a single value
Inv == \A vi,vj \in decided : vi = vj

TypeOK == 
    /\ vote \in [Node -> Value \cup {Nil}]
    /\ voted \in [Node -> BOOLEAN]
    /\ decided \in SUBSET Value

Symmetry == Permutations(Node)

\*
\* Weakest precondition.
\*

(**

Inv == \A vi,vj \in decided : vi = vj
wp(Next, Inv) ==
    /\ ENABLED CastVote(i,v) => wp(Post(CastVote), Inv)
    /\ ENABLED Decide(v,Q)   => wp(Post(Decide), Inv)

A1 == wp(Decide, Inv) ==
    /\ \A v \in Value, Q \in Quorum : 
        \A n \in Q : (vote[n] = v) => \A vi,vj \in (decided \cup {v}) : vi = vj

A2 == wp(CastVote, A1) ==
    \A i \in Node, v \in Value :
        ~voted[i] => 
            \A vz \in Value, Q \in Quorum : 
            \A n \in Q : ([vote EXCEPT ![i] = v][n] = vz) => \A vi,vj \in (decided \cup {vz}) : vi = vj

A3 == wp(Decide, A1) ==
    \A v \in Value, Q \in Quorum :
        (\A n \in Q : vote[n] = v) => 
            \A vz \in Value, Q \in Quorum : 
            \A n \in Q : (vote[n] = vz) => \A vi,vj \in ((decided \cup {v}) \cup {vz}) : vi = vj

**)

\* Inductive strengthening conjuncts
Inv150_1_0_def == \A s,t \in Node : \A Q \in Quorums : \A v \in Value : \E n \in Q : (voted[s]) \/ (~(vote[s] = v))
Inv65_1_1_def == \A s,t \in Node : \A Q \in Quorums : \A v \in Value : \E n \in Q : (vote[n] = v) \/ (~(v \in decided))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv150_1_0_def
  /\ Inv65_1_1_def

ASSUME QuorumType == Quorums \subseteq SUBSET Node
ASSUME NodeFinite == IsFiniteSet(Node)
ASSUME QuorumsAreNonEmpty == \A Q \in Quorums : Q # {}
ASSUME QuorumsIntersect == \A Q1,Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME NilType == Nil \notin Value

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY DEF vars, Quorums, CastVote, Decide, Init, Next, NextUnchanged, Inv, TypeOK, Symmetry, Inv150_1_0_def, Inv65_1_1_def, IndAuto
====
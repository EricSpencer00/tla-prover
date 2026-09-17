---- MODULE 20_naive_consensus ----
\* benchmark: ex-naive-consensus

EXTENDS TLAPS, FiniteSetTheorems, TLC

CONSTANT Node
CONSTANT Quorum
CONSTANT Value

VARIABLE vote
VARIABLE decide
VARIABLE decision

vars == <<vote,decide,decision>>

VotedFor(v) == \E Q \in Quorum : <<Q,v>> \in decide

CastVote(n, v) ==
    /\ \A x \in Value : <<n,x>> \notin vote
    /\ vote' = vote \cup {<<n,v>>}
    /\ UNCHANGED <<decide, decision>>

CollectVotes(Q, v) ==
    /\ \A n \in Q : <<n,v>> \in vote
    /\ decide' = decide \cup {<<Q,v>>}
    /\ UNCHANGED <<vote, decision>>

LearnValue(Q, v) ==
    /\ <<Q,v>> \in decide
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<vote, decide>>

Init == 
    /\ vote = {}
    /\ decide = {}
    /\ decision = {}

Next == 
    \/ \E n \in Node, v \in Value : CastVote(n,v)
    \/ \E Q \in Quorum, v \in Value : CollectVotes(Q,v)
    \/ \E Q \in Quorum, v \in Value : LearnValue(Q,v)

NextUnchanged == UNCHANGED vars

TypeOK == 
    /\ vote \in SUBSET (Node \X Value)
    /\ decide \in SUBSET (Quorum \X Value)
    /\ decision \in SUBSET Value

\* \* TODO: May need to fix this.
\* TypeOKRandom ==
\*     /\ vote \in RandomSubset(20, SUBSET (Node \X Value))
\*     /\ decide \in RandomSubset(20, SUBSET (Quorum \X Value))
\*     /\ decide \in SUBSET Value

Safety == \A v1,v2 \in Value : (v1 \in decision /\ v2 \in decision) => (v1=v2)

Symmetry == Permutations(Node) \cup Permutations(Value)


\* Inductive strengthening conjuncts
Inv255_1_0_def == \A VARA \in Value : (VotedFor(VARA)) \/ (~(VARA \in decision))
Inv1230_2_1_def == \A VARS \in Node : \A VARA \in Value : \A VARQ \in Quorum : (<<VARS,VARA>> \in vote) \/ (~(<<VARQ,VARA>> \in decide) \/ (~(VARS \in VARQ /\ vote = vote)))
Inv217_2_2_def == \A VARS \in Node : \A VARA \in Value : \A VARB \in Value : ((VARA=VARB) /\ vote = vote) \/ (~(<<VARS,VARA>> \in vote) \/ (~(<<VARS,VARB>> \in vote)))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv255_1_0_def
  /\ Inv1230_2_1_def
  /\ Inv217_2_2_def


AXIOM QuorumsAreNodePowersets == Quorum \subseteq SUBSET Node
AXIOM QuorumsOverlap == \A Q1,Q2 \in Quorum : Q1 \cap Q2 # {}
AXIOM Nonempty == Node # {} /\ Quorum # {} /\ Value # {}

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY SMT
====
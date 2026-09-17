---- MODULE 28_majorityset_leader_election ----
\* benchmark: ex-majorityset-leader-election

EXTENDS FiniteSetTheorems, TLAPS, TLC

CONSTANT Node

VARIABLE vote
VARIABLE leader
VARIABLE voters

vars == <<vote,leader,voters>>

\* The set of node majorities.
Majority == {i \in SUBSET(Node) : Cardinality(i) * 2 > Cardinality(Node)}

DidNotVote(n) == vote[n] = {}

Voting(n1,n2) ==
    /\ DidNotVote(n1)
    /\ vote' = [vote EXCEPT ![n1] = @ \cup {n2}]
    /\ UNCHANGED <<leader,voters>>

ReceiveVote(voter,n,vs) ==
    /\ n \in vote[voter]
    /\ voters[n] = vs
    /\ voter \notin vs
    /\ voters' = [voters EXCEPT ![n] = vs \cup {voter}]
    /\ UNCHANGED <<vote,leader>>

BecomeLeader(n, vs) ==
    /\ voters[n] = vs
    /\ vs \in Majority
    /\ leader' = leader \cup {n}
    /\ UNCHANGED <<vote,voters>>

Next ==
    \/ \E n1,n2 \in Node : Voting(n1,n2)
    \/ \E voter,n \in Node, vs \in SUBSET Node : ReceiveVote(voter,n,vs)
    \/ \E n \in Node, vs \in SUBSET Node : BecomeLeader(n, vs)

EmptySet == {}

Init ==
    /\ vote = [n \in Node |-> {}]
    /\ leader = {}
    /\ voters = [n \in Node |-> {}]

TypeOK ==
    /\ vote \in [Node -> SUBSET Node]
    /\ leader \in SUBSET Node
    /\ voters \in [Node -> SUBSET Node]

\* TypeOKRandom ==
\*     /\ vote \in RandomSubset(50, [Node -> SUBSET Node])
\*     /\ leader \in RandomSubset(8, SUBSET Node)
\*     /\ voters \in RandomSubset(35, [Node -> SUBSET Node])

Safety == \A x,y \in Node : (x \in leader) /\ (y \in leader) => (x = y)

Symmetry == Permutations(Node)

NextUnchanged == UNCHANGED vars

\* Inductive strengthening conjuncts
Inv172_1_0_def == \A VARI \in Node : \A VARJ \in Node : (VARI \in vote[VARJ]) \/ (~(VARJ \in voters[VARI]))
Inv396_1_1_def == \A VARI \in Node : (voters[VARI] \in Majority) \/ (~(VARI \in leader))
Inv1537_2_2_def == \A VARI \in Node : \A VARJ \in Node : \A VARK \in Node : (VARI = VARK /\ vote = vote) \/ (~(VARI \in vote[VARJ])) \/ (~(VARK \in vote[VARJ]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Safety
  /\ Inv172_1_0_def
  /\ Inv396_1_1_def
  /\ Inv1537_2_2_def


ASSUME MajorityIntersect == \A m1,m2 \in Majority : m1 \cap m2 # {}
ASSUME MajorityNonEmpty == Majority # {} /\ \A s \in Majority : s # {}
ASSUME NodeFinite == IsFiniteSet(Node) /\ Node # {}
ASSUME NatTimesTwoIneq == \A a,b \in Nat : (a >= b) => (a*2 >= b*2)
ASSUME NatIneqTrans == \A a,b,c \in Nat : (a >= b /\ b > c) => (a > c)

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY SMT, NatTimesTwoIneq, NatIneqTrans, SetExtensionality
====